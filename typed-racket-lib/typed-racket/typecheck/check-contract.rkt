#lang racket/unit
(require racket/match
         racket/dict
         racket/list
         racket/pretty
         racket/sequence
         racket/function
         syntax/id-table
         syntax/parse
         "../utils/utils.rkt"
         (typecheck check-below)
         (env global-env type-alias-helper type-env-structs lexical-env)
         (types subtype abbrev tc-result match-expanders union numeric-tower
                pairwise-intersect)
         (only-in (infer infer) meet join)
         (utils tc-utils contract-utils)
         (rep type-rep prop-rep)
         (private syntax-properties)
         "signatures.rkt"
         (for-syntax racket/base))

(import tc-expr^)
(export check-contract^)

;; trawl-for-doms/rng : syntax predicate predicate -> (listof syntax)
;; Finds syntax/subforms for which is-dom/rng? returns a non-#f value. Does not
;; recur into arrow subforms, according to is-arrow? since those must still be
;; typechecked. Do not call with an arrow that is also a domain/range, that will
;; infinite loop.
(define (trawl-for-doms/rng form is-dom/rng? is-arrow?)
  #;(pretty-print (syntax->datum form))
  (syntax-parse form
    [_
     #:when (is-dom/rng? form)
     (list form)]
    [(forms ...)
     (define-values (arrows non-arrows)
       (for/fold ([arrows '()]
                  [non-arrows '()])
                 ([form (in-list (syntax->list #'(forms ...)))])
         (syntax-parse form
           [_
            ;; we only want arrows that match the predicate; e.g. when looking
            ;; for the rng we have to make sure we don't grab a dom
            #:when (and (is-arrow? form) (is-dom/rng? form))
            (values (cons form arrows) non-arrows)]
           [_
            #:when (is-arrow? form)
            (values arrows non-arrows)]
           [_ (values arrows (cons form non-arrows))])))
     (for/fold ([doms/rng arrows])
               ([non-arrow (in-list non-arrows)])
       (append doms/rng (trawl-for-doms/rng non-arrow is-dom/rng? is-arrow?)))]
    [_ '()]))

;; tc-arrow-contract : syntax -> (Con t)
(define (tc-arrow-contract form)
  (define arrow-subforms (or (syntax->list form) (list)))

  (when (empty? arrow-subforms)
    (int-err "no subforms for given -> contract form ~a" form))
  (define is-arrow? (syntax-parser [:ctc:arrow^ #t] [_ #f]))
  (define doms
    (append*
     (map
      (λ (form) (trawl-for-doms/rng form ctc:arrow-dom-property is-arrow?))
      arrow-subforms)))
  (define sorted-doms (sort doms < #:key ctc:arrow-dom-property))
  (define is-rng? (syntax-parser [:ctc:arrow-rng^ #t] [_ #f]))
  (define rng*
    (append* (map
              (λ (form) (trawl-for-doms/rng form is-rng? is-arrow?))
              arrow-subforms)))
  (when (not (= 1 (length rng*)))
    (int-err "got more than one rng when typechecking -> contract"))
  (define rng (first rng*))

  (define-values (in-doms out-doms)
    (for/lists (ins outs)
               ([dom (in-list sorted-doms)])
      (define dom-ty (coerce-to-con (tc-expr/t dom)))
      (values (Con*-in-ty dom-ty) (Con*-out-ty dom-ty))))
  (define rng-ty (coerce-to-con (tc-expr/t rng)))
  (ret (-Con (->* out-doms (Con*-in-ty rng-ty))
             (->* in-doms (Con*-out-ty rng-ty)))))


;; tc-arrow-i-contract : syntax -> (Con t)

;; v2 pseudocode/notes

;; main data structure: list of expanded ctc forms first

;; 1) topo-sort this list via a helper function, and then the type rule will
;; just operate on that sorted list

;; Note: we'll still have to handle the surface/expanded dep list association, but
;; that will be common code b/w the doms and multi-value range checking

;; 2) When checking the current contract (call it "sub"), we must extend the
;; environment with a mapping from each of sub's dependencies' expanded
;; identifiers to their output types -- this is the identifier that is in the
;; body of the expanded contract (not the surface identifier). That mapping
;; couldn't have happened prior to checking sub because no dependency knows its
;; own expanded identifier (due to how ->i expands, we place the dependencies'
;; identifiers in the body of the contract for later recovery post-expansion;
;; without that trick, maybe a walk over the entire expanded syntax from ->i
;; could recover this; maybe there's even other macro-trickery to simplify this
;; further). Thus, after checking any contract, we pass along its full type by
;; mapping its surface identifier to that type. This works because all contracts
;; know their own surface identifier and all contracts know the surface
;; identifiers of their dependencies.

;; topo-sort-ctcs : (Listof Stx) (Stx -> Id) (Stx -> Listof Id) -> Listof Stx
;; Returns a permutation of ctcs in topo-order, according to their dependencies
(define (topo-sort-ctcs ctcs ctc->id ctc->deps)
  (define dep-map (for/list ([ctc ctcs])
                    (define surface-id (ctc->id ctc))
                    (define deps (or (ctc->deps ctc) (list)))
                    (cons surface-id deps)))
  ;; TODO: could find-strongly-connected-type-aliases ever not return something
  ;; we want to just outright flatten? e.g. could we even get to this point if
  ;; there was a cycle (or would ->i have already errored)?
  (define sorted-ids* (flatten (find-strongly-connected-type-aliases dep-map)))
  (define topo-sorted-ids (reverse sorted-ids*))

  (define ((ctc-matcher-for-id id) ctc) (free-identifier=? id (ctc->id ctc)))
  (for/list ([id topo-sorted-ids])
    (findf (ctc-matcher-for-id id) ctcs)))

(define ((mk/lookup-fail-in name) id)
  (int-err (format "couldn't find ~a in ~a" id name)))

(define (tc-arrow-i-contract form)
  (define arrow-subforms (or (syntax->list form) (list)))
  (when (empty? arrow-subforms)
    (int-err "no subforms for given ->i form ~a" form))
  (define is-arrow-i? (syntax-parser [:ctc:arrow-i^ #t] [_ #f]))
  (define expanded-doms
    (remove-duplicates
     (append*
      (map
       (λ (form) (trawl-for-doms/rng form ctc:arrow-i-dom-property is-arrow-i?))
       arrow-subforms))
     equal?
     #:key (lambda (ctc) (dom-info-type (ctc:arrow-i-dom-property ctc)))))
  (define rest-ctc/#f
    (match (trawl-for-doms/rng form ctc:arrow-i-rest-property is-arrow-i?)
      [(list rest-ctc) rest-ctc]
      [_ #f]))

  (define dom-ctc->id (compose dom-info-id ctc:arrow-i-dom-property))
  (define dom-ctc->deps (compose dom-info-deps ctc:arrow-i-dom-property))
  (define (rest-ctc->dom-ctc rest-ctc)
    (define rest (ctc:arrow-i-rest-property rest-ctc))
    (ctc:arrow-i-dom-property
     rest-ctc
     (dom-info
      (rest-info-id rest)
      (rest-info-deps rest)
      (rest-info-ctc rest)
      +inf.0
      #t)))
  (define rngs
    (remove-duplicates
     (append*
      (map
       (λ (form) (trawl-for-doms/rng form ctc:arrow-i-rng-property is-arrow-i?))
       arrow-subforms))
     =
     #:key (lambda (ctc) (rng-info-index (ctc:arrow-i-rng-property ctc)))))
  (when (zero? (length rngs))
    (int-err "no range contract found when typechecking ->i expansion"))
  (define dom? ctc:arrow-i-dom-property)
  (define rng-ctc->id (compose rng-info-id ctc:arrow-i-rng-property))
  (define rng-ctc->deps (compose rng-info-deps ctc:arrow-i-rng-property))
  (define (dom/rng-ctc->id ctc)
    (if (dom? ctc)
        (dom-ctc->id ctc)
        (rng-ctc->id ctc)))
  (define (dom/rng-ctc->deps ctc)
    (if (dom? ctc)
        (dom-ctc->deps ctc)
        (rng-ctc->deps ctc)))
  (define ctcs (append expanded-doms rngs))
  (define-values (topo-sorted-dom-ctcs topo-sorted-rng-ctcs)
    (partition
     dom?
     (topo-sort-ctcs (if rest-ctc/#f
                         ;; Typechecking #:rest arguments is similar enough to
                         ;; typechecking other domain arguments that we can
                         ;; typecheck them both uniformly. We simply cons it to
                         ;; the other contracts because topo-sort-ctcs doesn't
                         ;; care about the order of its input.
                         (cons (rest-ctc->dom-ctc rest-ctc/#f) ctcs)
                         ctcs)
                     dom/rng-ctc->id
                     dom/rng-ctc->deps)))

  ;; check-subcontract : Stx (Stx -> Listof Stx) Env -> Type/c
  ;; Calculates the type of ctc. All its dependencies must have their surface
  ;; id mapped to their contract type in env.
  (define (check-subcontract ctc ctc->deps env)
    (define surface-deps (or (ctc->deps ctc) (list)))
    (define-values (expanded-deps expanded-ctc)
      (syntax-parse ctc
        [(_ deps ... ctc)
         (values #'(deps ...) #'ctc)]))
    (define lookup-fail (mk/lookup-fail-in "deps-env"))
    (define deps-env
      (for/fold ([env env])
                ([surface-id surface-deps]
                 [expanded-id (in-syntax expanded-deps)])
        (extend env expanded-id (Con*-out-ty (lookup env surface-id lookup-fail)))))
    (with-lexical-env deps-env
      (coerce-to-con (tc-expr/t expanded-ctc))))

  (define doms-checked-env
    (for/fold ([env (lexical-env)])
              ([ctc topo-sorted-dom-ctcs])
      (define ctc-ty (check-subcontract ctc dom-ctc->deps env))
      (extend env (dom-ctc->id ctc) ctc-ty)))

  (define rest-ctc-ty/#f
    (match (and rest-ctc/#f
                (lookup
                 doms-checked-env
                 (rest-info-id (ctc:arrow-i-rest-property rest-ctc/#f))
                 (mk/lookup-fail-in "doms-checked-env")))
      [#f #f]
      [(and t (Con*: (Listof: _) (Listof: _))) t]
      [non-list-ty
       (tc-error/fields
        "#:rest contract must be a list contract"
        #:delayed? #t
        "#:rest contract type" non-list-ty)
       (-Con (make-Listof Univ) (make-Listof (Un)))]))

  ;; if we didn't care about the order of error messages, we could check all
  ;; of the conditions using rng-checked-env
  (define (check-pre/post expr env expr->deps expr->desc?)
    (define-values (expanded-deps expanded-expr)
      (syntax-parse expr
        [(_ () deps ... expr)
         (values #'(deps ...) #'expr)]))
    (define lookup-fail (mk/lookup-fail-in "pre/post deps-env"))
    (define surface-deps (or (expr->deps expr) (list)))
    (define deps-env
      (for/fold ([env env])
                ([surface-id surface-deps]
                 [expanded-id (in-syntax expanded-deps)])
        (extend env expanded-id (Con*-out-ty (lookup env surface-id lookup-fail)))))
    (with-lexical-env deps-env
      (tc-expr/check expanded-expr (ret
                                    (if (expr->desc? expr)
                                        (Un -Boolean -String (-lst -String))
                                        Univ)))))
    
  (define is-pre? ctc:arrow-i-pre-property)
  (define (pre-dont-recur? form)
    (or (is-arrow-i? form) (is-pre? form)))
  (define pres
    (append*
     (map
      (λ (form) (trawl-for-subs form pre-dont-recur? is-pre?))
      arrow-subforms)))
  (define pre->deps (compose pre-info-deps ctc:arrow-i-pre-property))
  (define pre->position (compose pre-info-position ctc:arrow-i-pre-property))
  (define pre->desc? (compose pre-info-desc? ctc:arrow-i-pre-property))
  (for-each (λ (p) (check-pre/post p doms-checked-env pre->deps pre->desc?))
            (sort pres < #:key pre->position))

  (define rng-checked-env
    (for/fold ([env doms-checked-env])
              ([ctc topo-sorted-rng-ctcs])
      (define ctc-ty (check-subcontract ctc rng-ctc->deps env))
      (extend env (rng-ctc->id ctc) ctc-ty)))
  (define rng-ctcs (sort rngs < #:key (compose rng-info-index ctc:arrow-i-rng-property)))
  (define-values (rng-in-tys rng-out-tys)
    (for/lists (in-tys out-tys)
               ([ctc rng-ctcs])
      (define lookup-fail (mk/lookup-fail-in "rng-checked-env"))
      ;; TODO: we're calling check-subcontract twice by calling it here, but I'm
      ;; not sure of another way to handle the two cases: a) when the ctc has
      ;; deps, rng-checked-env doesn't contain entries for its expanded deps
      ;; which makes calling tc-expr/t not work b) when the ctc is unnamed, we
      ;; can't look its type up in rng-checked-env because it has no id
      (define ctc-ty (check-subcontract ctc rng-ctc->deps rng-checked-env))
      (values (Con*-in-ty ctc-ty) (Con*-out-ty ctc-ty))))

  (define is-post? ctc:arrow-i-post-property)
  (define (post-dont-recur? form)
    (or (is-arrow-i? form) (is-post? form)))
  (define posts
    (append*
     (map
      (λ (form) (trawl-for-subs form post-dont-recur? is-post?))
      arrow-subforms)))
  (define post-infos (map ctc:arrow-i-post-property posts))
  (define post->deps (compose post-info-deps ctc:arrow-i-post-property))
  (define post->desc? (compose post-info-desc? ctc:arrow-i-post-property))
  (define post->position (compose post-info-position ctc:arrow-i-post-property))
  (for-each (λ (p) (check-pre/post p rng-checked-env post->deps post->desc?))
            (sort posts < #:key post->position))


  (define dom-infos (map ctc:arrow-i-dom-property expanded-doms))
  (define-values (kw-doms plain-doms)
    (partition (compose keyword? dom-info-type) dom-infos))
  (define-values (reqd-plain-doms opt-plain-doms)
    (partition dom-info-mandatory? (sort plain-doms < #:key dom-info-type)))
  (define sorted-kw-doms (sort kw-doms keyword<? #:key dom-info-type))
  (define opt-count (length opt-plain-doms))
  (define-values (in-arrs out-arrs)
    (for/lists (ins outs)
               ([vararg-slice-length (in-range (add1 opt-count))])
      (define opts (take opt-plain-doms vararg-slice-length))
      (define doms (append reqd-plain-doms opts))
      (define lookup-fail (mk/lookup-fail-in "doms-checked-env"))
      (define (dom-ty d) (lookup doms-checked-env (dom-info-id d) lookup-fail))
      (define ((kw-in/out Con*in/out-ty) kw-info)
        (define kw (dom-info-type kw-info))
        (define ty (lookup doms-checked-env (dom-info-id kw-info) lookup-fail))
        (make-Keyword kw (Con*in/out-ty ty) (dom-info-mandatory? kw-info)))
      ;; Assumes list-ty is a list type. The usages in the make-arr* below are
      ;; guarded by the list-ctc-ty? check above.
      (define (list-contents-ty list-ty)
        (match list-ty
          [(Listof: ty) ty]))
      (values
       (make-arr* (map (compose Con*-out-ty dom-ty) doms)
                  (make-Values (map (λ (ty) (-result ty -tt-propset -empty-obj)) rng-in-tys))
                  #:rest (and rest-ctc-ty/#f
                              (list-contents-ty (Con*-out-ty rest-ctc-ty/#f)))
                  #:kws (map (kw-in/out Con*-out-ty) sorted-kw-doms))
       (make-arr* (map (compose Con*-in-ty dom-ty) doms)
                  (make-Values (map (λ (ty) (-result ty -tt-propset -empty-obj)) rng-out-tys))
                  #:rest (and rest-ctc-ty/#f
                              (list-contents-ty (Con*-in-ty rest-ctc-ty/#f)))
                  #:kws (map (kw-in/out Con*-in-ty) sorted-kw-doms)))))
  (ret (-Con (make-Function in-arrs) (make-Function out-arrs))))

;; trawl-for-subs : syntax -> (list syntax)
;; Don't call with a dont-recur? that is also is-sub?
(define (trawl-for-subs form dont-recur? is-sub?)
  (syntax-parse form
    [_
     #:when (is-sub? form)
     (list form)]
    [(forms ...)
     (for/fold ([subs '()])
               ([form (in-list (syntax->list #'(forms ...)))])
       (syntax-parse form
         [_
          #:when (and (dont-recur? form)
                      (is-sub? form))
          (cons form subs)]
         [_ (append subs (trawl-for-subs form dont-recur? is-sub?))]))]
    [_ '()]))

;; tc-and/c : syntax -> (Con t)
(define (tc-and/c form)
  (define subs (sort (trawl-for-subs (ctc:and/c-sub-property form #f)
                                      (syntax-parser [:ctc:and/c^ #t]
                                                     [_ #f])
                                      ctc:and/c-sub-property)
                      <
                      #:key ctc:and/c-sub-property))
  (define subs-tys (map (compose coerce-to-con tc-expr/t) subs))
  (define-values (in-ty out-ty)
    (if (empty? subs-tys)
        (values Univ Univ)
        (for/fold ([in-ty (Con*-in-ty (first subs-tys))]
                   [out-ty (Con*-out-ty (first subs-tys))])
                  ([ty (in-list (rest subs-tys))])
          (define next-in-ty (Con*-in-ty ty))
          (unless (subtype out-ty next-in-ty)
            (tc-error/fields
             "preceding contract's output type does not match the next input type"
             #:delayed? #f
             "previous output type" out-ty
             "next input type" next-in-ty))
          (values in-ty (pairwise-intersect out-ty (Con*-out-ty ty))))))
  (ret (-Con in-ty out-ty)))

;; tc-or/c : syntax -> (Con t)
(define (tc-or/c form)
  (define subs (sort (trawl-for-subs (ctc:or/c-sub-property form #f)
                                     (syntax-parser [:ctc:or/c^ #t]
                                                    [_ #f])
                                     ctc:or/c-sub-property)
                     <
                     #:key ctc:or/c-sub-property))
  (define-values (in-ty out-ty)
    (for/fold ([in-ty Univ]
               [out-ty (Un)])
              ([sub (in-list subs)])
      (define con-ty (coerce-to-con (tc-expr/t sub)))
      (values
       (meet in-ty (Con*-in-ty con-ty))
       (join out-ty (Con*-out-ty con-ty)))))
  (ret (-Con in-ty out-ty)))

;; tc-list/c : syntax -> (Con t)
(define (tc-list/c form)
  (define subs (sort (trawl-for-subs (ctc:list/c-sub-property form #f)
                                     (syntax-parser [:ctc:list/c^ #t]
                                                    [_ #f])
                                     ctc:list/c-sub-property)
                     <
                     #:key ctc:list/c-sub-property))
  (define-values (in-tys out-tys)
    (for/lists (ins outs)
               ([sub (in-list subs)])
      (define con-ty (coerce-to-con (tc-expr/t sub)))
      (values (Con*-in-ty con-ty) (Con*-out-ty con-ty))))
  (ret (match* (in-tys out-tys)
         [((list) (list))
          (-Con Univ (-lst*))]
         [((list _ _ ...) (list _ _ ...))
          (-Con (apply -lst* in-tys) (apply -lst* out-tys))])))

(define (coerce-to-con ty)
  (define coercible-simple-value-types
    (Un -Null -Symbol -Boolean -Keyword -Char -Bytes -String -Number))
  [match ty
    [(Con*: t _) ty]
    [(ConFn*: in-ty out-ty)
     (-FlatCon in-ty out-ty)]
    [_
     #:when (subtype ty coercible-simple-value-types)
     (-FlatCon Univ ty)]
    ;; Because the type of these isn't the core type needed for the contract,
    ;; they need to be handled differently than coercible-simple-value-types
    [(== -Regexp) (-FlatCon Univ -String)]
    [(== -Byte-Regexp) (-FlatCon Univ -Bytes)]
    [_ (tc-error/fields "could not coerce to a contract type"
                        #:delayed? #t
                        "type" ty)
       (-Con (Un) Univ)]])
