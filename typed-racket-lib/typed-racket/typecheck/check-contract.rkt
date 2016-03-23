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
         (env global-env type-alias-helper type-env-structs lexical-env)
         (types subtype abbrev tc-result match-expanders union numeric-tower)
         (only-in (infer infer)
                  meet join)
         (utils tc-utils contract-utils)
         (rep type-rep filter-rep)
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
                    ;; TODO: what if the id was #f, maybe gensym an id here?
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
     free-identifier=?
     #:key (lambda (ctc) (dom-info-id (ctc:arrow-i-dom-property ctc)))))
  (define rest-ctc/#f
    (ormap
     (λ (x) x)
     (trawl-for-doms/rng form ctc:arrow-i-rest-property is-arrow-i?)))

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
  (define topo-sorted-dom-ctcs
    (topo-sort-ctcs (if rest-ctc/#f
                        (cons (rest-ctc->dom-ctc rest-ctc/#f) expanded-doms)
                        expanded-doms)
                    dom-ctc->id
                    dom-ctc->deps))

  ;; check-subcontract : Stx (Stx -> Listof Stx) Env -> Type/c
  ;; Calculates the type of ctc. All its dependencies must have their surface
  ;; id mapped to their contract type in env.
  (define (check-subcontract ctc ctc->deps env)
    (define surface-deps (or (ctc->deps ctc) (list)))
    (define-values (expanded-deps expanded-ctc)
      (syntax-parse ctc
        [(_ deps ... ctc)
         (values #'(deps ...) #'ctc)]))
    (define deps-env
      (for/fold ([env env])
                ([surface-id surface-deps]
                 [expanded-id (in-syntax expanded-deps)])
        (extend env expanded-id (Con*-out-ty (lookup env surface-id void)))))
    (with-lexical-env deps-env
      (coerce-to-con (tc-expr/t expanded-ctc))))

  (define doms-checked-env
    (for/fold ([env (lexical-env)])
              ([ctc topo-sorted-dom-ctcs])
      (define ctc-ty (check-subcontract ctc dom-ctc->deps env))
      ;; TODO: what if dom-ctc->id contains #f (dom-info-id can be #f)
      (extend env (dom-ctc->id ctc) ctc-ty)))

  ;; We check the type of the #:rest contract after building up the checked-env
  ;; because it would be complicated to check that it's a list contract in the
  ;; middle of checking the rest of the contracts.
  (define rest-ctc-ty/#f
    (and rest-ctc/#f
         (let ([surface-id (rest-info-id (ctc:arrow-i-rest-property rest-ctc/#f))])
           (lookup doms-checked-env surface-id void))))
  (define (list-ctc-ty? ty)
    (match (coerce-to-con ty)
      ;; TODO: Figure out why the more natural version of this match causes a
      ;; "unbound identifier in module" bug that I can't really track down
      ;;[(Con*: (Listof: _) (Listof: _)) #t]
      [(Con*: in out)
       (match* (in out)
         [((Listof: _) (Listof: _)) #t]
         [(_ _) #f])]
      [_ #f]))
  (when (and rest-ctc-ty/#f (not (list-ctc-ty? rest-ctc-ty/#f)))
    (define ty rest-ctc-ty/#f)
    ;; TODO: remove this hack. We want the above error to be delayed but need
    ;; the pattern match for make-arr* below to not blow up / signal a duplicate
    ;; error.
    (set! rest-ctc-ty/#f (-Con (make-Listof (Un)) (make-Listof Univ)))
    (tc-error/fields
     "#:rest contract must be a list contract"
     #:delayed? #t
     "#:rest contract type" ty))

  (define possible-rngs
    (append*
     (map
      (λ (form) (trawl-for-doms/rng form ctc:arrow-i-rng-property is-arrow-i?))
      arrow-subforms)))
  (when (zero? (length possible-rngs))
    (int-err "no range contract found when typechecking ->i expansion"))
  (define rng-ctc (first possible-rngs))
  (define rng-ctc->deps (compose rng-info-deps ctc:arrow-i-rng-property))
  (define rng-ctc-ty (check-subcontract rng-ctc rng-ctc->deps doms-checked-env))

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
      ;; TODO: dom-ty should be able to look up the type in doms-checked-env
      (define (dom-ty d) (lookup doms-checked-env (dom-info-id d) void))
      (define ((kw-in/out Con*in/out-ty) kw-info)
        (define kw (dom-info-type kw-info))
        (define ty (lookup doms-checked-env (dom-info-id kw-info) void))
        (make-Keyword kw (Con*in/out-ty ty) (dom-info-mandatory? kw-info)))
      ;; Assumes list-ty is a list type. The usages in the make-arr* below are
      ;; guarded by the list-ctc-ty? check above.
      (define (list-contents-ty list-ty)
        (match list-ty
          [(Listof: ty) ty]))
      (values
       (make-arr* (map (compose Con*-out-ty dom-ty) doms)
                  (Con*-in-ty rng-ctc-ty)
                  #:rest (and rest-ctc-ty/#f
                              (list-contents-ty (Con*-out-ty rest-ctc-ty/#f)))
                  #:kws (map (kw-in/out Con*-out-ty) sorted-kw-doms))
       (make-arr* (map (compose Con*-in-ty dom-ty) doms)
                  (Con*-out-ty rng-ctc-ty)
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
          (values in-ty (meet out-ty (Con*-out-ty ty))))))
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
       ;; XXX: simply taking the meet might not work for higher-order contracts,
       ;; even if it did turn arrows into a case->. so, there may need to be
       ;; some extra work to support higher-order contracts in or/c
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
    ;; TODO: replace this with an error
    [_ (tc-error/fields "could not coerce to a contract type"
                        #:delayed? #t
                        "type" ty)]])

;; check-contract : identifier syntax -> [void]
(define (check-contract defn-id ctc)
  (match-define (Con*: in-ty _) (coerce-to-con (tc-expr/t ctc)))
  (unless (subtype (lookup-type defn-id) in-ty)
    (tc-error/fields "contract is incompatible with type"
                     #:delayed? #t
                     "id" (syntax->datum defn-id)
                     "type" (lookup-type defn-id)
                     "contract type" (coerce-to-con (tc-expr/t ctc)))))
