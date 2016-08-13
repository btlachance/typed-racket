#lang racket/unit

;; This module provides a unit for typechecking contracts. The points of entry
;; are two functions check-contract-app and check-contract.

;; Each type rule for contracts proceeds by finding annotated pieces of syntax
;; in the expansion. The typed versions of the contract forms (those in
;; (base-env contract-prims)) annotate the surface syntax before delegating to
;; the untyped form. The typechecking rules in this unit are where we finally
;; use those annotations.

(require racket/match
         racket/list
         racket/function
         racket/sequence
         syntax/parse
         "../utils/utils.rkt"
         (env type-alias-helper type-env-structs lexical-env)
         (types subtype abbrev tc-result match-expanders union numeric-tower
                pairwise-intersect)
         (typecheck check-below)
         (only-in (infer infer) meet join)
         (utils tc-utils contract-utils)
         (rep type-rep)
         (private syntax-properties)
         "signatures.rkt")

(import tc-expr^)
(export check-contract^)

(define (check-contract-app ctc to-protect [expected #f])
  (define ctc-ty (coerce-to-con (tc-expr/t ctc)))
  (define val-ty (tc-expr/t to-protect))
  (check-below val-ty (Con*-in-ty ctc-ty))
  (ret (pairwise-intersect val-ty (Con*-out-ty ctc-ty))))

(define (check-contract form [expected #f])
  (define rule (tr:ctc-property form))
  (match rule
    ['-> (tc-arrow-contract form)]
    ['->i (tc-arrow-i-contract form)]
    ['and/c (tc-and/c form)]
    ['or/c (tc-or/c form)]
    ['list/c (tc-list/c form)]
    [_ (int-err "unknown contract form ~a" rule)]))


(define (tc-arrow-contract form)
  (define arrow-subforms (or (syntax->list form) (list)))

  (when (empty? arrow-subforms)
    (int-err "no subforms for given -> contract form ~a" form))
  (define (is-arrow? stx) (equal? (tr:ctc-property stx) '->))
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

;; trawl-for-doms/rng : syntax predicate predicate -> (listof syntax) Finds
;; syntax/subforms for which is-dom/rng? returns a non-#f value. Does not recur
;; into arrow subforms, according to is-arrow?, since those must still be
;; typechecked, and we do not want to mix the components of one arrow contract
;; with the components of another.
;; NOTE: Clients should not call with a form that is both is-dom/rng? and
;; is-arrow?. In that case, this will simply return a list containing the given
;; form and not its subforms. If they try to typecheck the result thinking it's
;; a *subform*, they will end up in an infinite loop between the arrow
;; typechecking rule and the higher-level typechecker.
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


;; The function tc-arrow-i-contract typechecks the expansion of the TR's ->i
;; macro. That macro annotates each sub-contract's RHS (e.g. the actual
;; domain/range contract) with its surface identifier, its relative position in
;; the function signature, whether it's mandatory, as well as a few more details
;; before delegating to Racket's ->i. tc-arrow-i-contract uses that information
;; to recover the order of each sub-contract so that it can typecheck them in
;; the correct order and determine the contract's type.

;; What makes this type rule difficult is that the typed ->i macro only sees
;; each contract's and its dependencies' surface syntax, which means that's all
;; it can put in the annotations for this function to recover---during
;; typechecking, though, all of the dependencies' identifiers in ->i's expansion
;; are not necessarily the same as the surface identifiers stored in the
;; annotation. To use the information from the typed ->i macro we must relate
;; the surface identifiers to the expanded identifiers.

;; Consider the following piece of the domain from an ->i use, [x (d1 d2) ctc],
;; which has name x, dependencies d1 and d2, and contract ctc. To support
;; correlating the surface dependency identifiers with the expanded identifiers,
;; TR's ->i macro rewrites ctc to (begin d1 d2 ctc) before delegating. This
;; allows the type rule to retrieve the expanded d1 and d2 and correlate them
;; with the surface versions stored in the annotation, at the cost of leaking
;; the result of this rewrite to the user when ->i raises errors about syntax
;; and contract violations.

(define (tc-arrow-i-contract form)
  (define arrow-subforms (or (syntax->list form) (list)))
  (when (empty? arrow-subforms)
    (int-err "no subforms for given ->i form ~a" form))
  (define (is-arrow-i? stx)
    (equal? (tr:ctc-property stx) '->i))
  (define doms
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

  ;; rest-ctc->dom-ctc produces a dom-info struct for the given rest contract's
  ;; rest-info. Useful for typechecking rest contracts which may depend on/be
  ;; depended on by the dom and rng contracts. Treating it as an extra dom
  ;; contract lets us typecheck the whole lot uniformly
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
  (define ctcs (append doms rngs))
  (define-values (topo-sorted-dom-ctcs topo-sorted-rng-ctcs)
    (partition
     dom?
     (topo-sort-ctcs (if rest-ctc/#f
                         (cons (rest-ctc->dom-ctc rest-ctc/#f) ctcs)
                         ctcs)
                     dom/rng-ctc->id
                     dom/rng-ctc->deps)))

  ;; check-subcontract : Stx (Stx -> Listof Stx) Env -> Type/c
  ;; Calculates the Con* type of ctc. All of ctc's dependencies must have their
  ;; surface id mapped to their Con* type in env. Uses ctc->deps to get the
  ;; deps' surface ids so that, after retrieving the deps' expanded ids from the
  ;; the (begin ...)-rewritten contract, it can update env with the appropriate
  ;; type for each expanded id based on its Con* type.
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

  ;; Calculates the type of the pre/post-condition expression. Exactly like
  ;; check-subcontract, each pre/post-condition must have its dep's surface id's
  ;; mapped to their Con* type in env.
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


  (define dom-infos (map ctc:arrow-i-dom-property doms))
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
      (define (list-contents-ty list-ty)
        (match list-ty
          [(Listof: ty) ty]))
      (values
       (make-arr* (map (compose Con*-out-ty dom-ty) doms)
                  (make-Values (map (λ (ty) (-result ty -tt-propset -empty-obj)) rng-in-tys))
                  #:rest (and rest-ctc-ty/#f
                              ;; at this point, we know rest-ctc-ty/#f will be
                              ;; given a list type
                              (list-contents-ty (Con*-out-ty rest-ctc-ty/#f)))
                  #:kws (map (kw-in/out Con*-out-ty) sorted-kw-doms))
       (make-arr* (map (compose Con*-in-ty dom-ty) doms)
                  (make-Values (map (λ (ty) (-result ty -tt-propset -empty-obj)) rng-out-tys))
                  #:rest (and rest-ctc-ty/#f
                              ;; ditto above remark about rest-ctc-ty/#f
                              (list-contents-ty (Con*-in-ty rest-ctc-ty/#f)))
                  #:kws (map (kw-in/out Con*-in-ty) sorted-kw-doms)))))
  (ret (-Con (make-Function in-arrs) (make-Function out-arrs))))

;; topo-sort-ctcs : (Listof Stx) (Stx -> Id) (Stx -> Listof Id) -> Listof Stx
;; Returns a permutation of ctcs in topo-order, according to their dependencies
(define (topo-sort-ctcs ctcs ctc->id ctc->deps)
  (define dep-map (for/list ([ctc ctcs])
                    (define surface-id (ctc->id ctc))
                    (define deps (or (ctc->deps ctc) (list)))
                    (cons surface-id deps)))
  (define sorted-ids* (flatten (find-strongly-connected-type-aliases dep-map)))
  (define topo-sorted-ids (reverse sorted-ids*))

  (define ((ctc-matcher-for-id id) ctc) (free-identifier=? id (ctc->id ctc)))
  (for/list ([id topo-sorted-ids])
    (findf (ctc-matcher-for-id id) ctcs)))

(define ((mk/lookup-fail-in name) id)
  (int-err (format "couldn't find ~a in ~a" id name)))

;; trawl-for-subs : syntax -> (list syntax)
;; Don't call with a dont-recur? that is also is-sub?; similar reason as with
;; trawl-for-doms/rng
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


(define (tc-and/c form)
  (define subforms (or (syntax->list form) (list)))
  (when (empty? subforms)
    (int-err "no subforms for given and/c form ~a" form))
  (define (is-and/c? stx) (equal? (tr:ctc-property stx) 'and/c))
  (define subs (sort (trawl-for-subs subforms
                                     is-and/c?
                                     (conjoin syntax? ctc:and/c-sub-property))
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

(define (tc-or/c form)
  (define subforms (or (syntax->list form) (list)))
  (when (empty? subforms)
    (int-err "no subforms for given or/c form ~a" form))
  (define (is-or/c? stx) (equal? (tr:ctc-property stx) 'or/c))
  (define subs (sort (trawl-for-subs subforms
                                     is-or/c?
                                     (conjoin syntax? ctc:or/c-sub-property))
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

(define (tc-list/c form)
  (define (is-list/c? stx) (equal? (tr:ctc-property stx) 'list/c))
  (define subs
    (match (syntax->list form)
      [(list subforms ...)
       (define subs* (trawl-for-subs subforms is-list/c?
                                     (conjoin syntax? ctc:list/c-sub-property)))
       (sort subs* < #:key ctc:list/c-sub-property)]
      [#f (int-err "no subforms for given list/c form ~a" form)]))

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
