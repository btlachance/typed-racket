#lang racket/unit
(require racket/match
         racket/dict
         racket/list
         racket/pretty
         racket/sequence
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

(define-match-expander Con*:
  (lambda (stx)
    (syntax-case stx ()
      [(_ t)
       #'(or (? FlatCon? (app FlatCon-ty t))
             (? Con? (app Con-ty t)))])))

;; compat? : Type Type -> Boolean
(define (compat? id-type ctc-type)
  (match* (id-type ctc-type)
    [(_
      (Con*: (== Univ)))
      #t]
    [((Function: (list (arr: s1s s2 _ _ _)))
      (Con*: (Function: (list (arr: t1s t2 _ _ _)))))
     (and (andmap compat? s1s t1s)
          (compat? s2 t2))]
    ;; Because we check subtype in both directions, have to explicitly disallow this
    [(s (or (Con*: t) t))
     #:when (or (equal? s (Un)) (equal? t (Un)))
     #f]
    [(s (or (Con*: t) t))
     ;; equal? maybe not necessary, we check subtype in both directions
     (or (equal? s t) (subtype s t) (subtype t s))]
    [(_ _) #f]))

;; TODO: Use this for check-contract, too. Something like:
;; (-Con (get-core-type t))
(define (get-core-type ty)
  (define coercible-simple-value-types
    (Un -Null -Symbol -Boolean -Keyword -Char -Bytes -String -Number))
  (match ty
    [(PredicateFilter: (FilterSet: (TypeFilter: t _) fs-))
     #:when (subtype ty (-> Univ Univ))
     t]
    [(Con*: t) t]
    ;; TODO: These should all be interpreted as FlatCon, but we have no control
    ;; over that via get-core-type. Need to restructure the code to accomodate
    ;; that.
    [_
     #:when (subtype ty coercible-simple-value-types)
     ty]
    ;; Because the type of these isn't the core type needed for the contract,
    ;; they need to be handled differently than coercible-simple-value-types
    [(== -Regexp) -String]
    [(== -Byte-Regexp) -Bytes]
    ;; See explanation in filter->contract
    ;[(Function: (list (arr: t (== -Boolean) _ _ _))) t]
    [_ (Un)]))

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
  (ret (-Con (->* (for/list ([dom (in-list sorted-doms)])
                    (get-core-type (tc-expr/t dom)))
                  (get-core-type (tc-expr/t (first rng*)))))))

;; tc-arrow-i-contract : syntax -> (Con t)
(define (tc-arrow-i-contract form)
  (define arrow-subforms (or (syntax->list form) (list)))
  (when (empty? arrow-subforms)
    (int-err "no subforms for given ->i form ~a" form))
  (define is-arrow-i? (syntax-parser [:ctc:arrow-i^ #t] [_ #f]))
  (define expanded-ctcs
    (remove-duplicates
     (append*
      (map
       (λ (form) (trawl-for-doms/rng form ctc:arrow-i-dom-property is-arrow-i?))
       arrow-subforms))
     free-identifier=?
     #:key (lambda (ctc) (dom-info-id (ctc:arrow-i-dom-property ctc)))))
  (define dom-infos (map ctc:arrow-i-dom-property expanded-ctcs))
  (define dom-ids (map dom-info-id dom-infos))

  ;; (list (list id dep ...) ...)
  (define dep-map (for/list ([info (in-list dom-infos)])
                    (define id (dom-info-id info))
                    (define deps (or (dom-info-deps info) (list)))
                    (cons id deps)))
  (define topo-sorted-dom-ids
    (reverse (flatten (find-strongly-connected-type-aliases dep-map))))

  (define dom-expanded-ctcs-by-id
    (for/hash ([ctc expanded-ctcs])
      (define info (ctc:arrow-i-dom-property ctc))
      (values (dom-info-id info) ctc)))

  (define dom-surface-deps-by-id
    (for/hash ([info dom-infos])
      (values (dom-info-id info) (or (dom-info-deps info) (list)))))

  (define doms-checked-env
    (for/fold ([env (lexical-env)])
              ([dom-id (in-list topo-sorted-dom-ids)])
      (define surface-deps (hash-ref dom-surface-deps-by-id dom-id))
      (define ctc* (hash-ref dom-expanded-ctcs-by-id dom-id))
      (define-values (expanded-deps ctc)
        (syntax-parse ctc*
          ;; ctc is transformed to (begin deps ... ctc) by ->i in contract-prims
          [(_ deps ... ctc)
           (values #'(deps ...) #'ctc)]))
      (define-values (expansion-ids tys)
        (for/lists (ids tys)
                   ([surface-dep (in-list surface-deps)]
                    [expanded-dep (in-syntax expanded-deps)])
          (values expanded-dep (lookup env surface-dep void))))
      (define env* (extend/values env expansion-ids tys))
      (extend env* dom-id
              (with-lexical-env env* (get-core-type (tc-expr/t ctc))))))
  (define possible-rngs
    (append*
      (map
       (λ (form) (trawl-for-doms/rng form ctc:arrow-i-rng-property is-arrow-i?))
       arrow-subforms)))
  (when (zero? (length possible-rngs))
    (int-err "no range contract found when typechecking ->i expansion"))
  (define rng-ctc* (first possible-rngs))
  (define-values (expanded-rng-deps rng-ctc)
    (syntax-parse rng-ctc*
      [(_ deps ... rng-ctc)
       (values #'(deps ...) #'rng-ctc)]))
  (define rng-info (ctc:arrow-i-rng-property rng-ctc*))
  (define surface-rng-deps (rng-info-deps rng-info))
  (define-values (rng-ids rng-tys) (for/lists (ids tys)
                                              ([surface-rng-dep (in-syntax surface-rng-deps)]
                                               [expanded-rng-dep (in-syntax expanded-rng-deps)])
                                     (values expanded-rng-dep (lookup doms-checked-env surface-rng-dep void))))
  (define final-env* (extend/values doms-checked-env rng-ids rng-tys))
  (define rng-id (rng-info-id rng-info))
  (define final-env
    (extend final-env* rng-id
            (with-lexical-env final-env* (get-core-type (tc-expr/t rng-ctc)))))

  (define-values (kw-dom-infos plain-dom-infos)
    (partition (lambda (info) (keyword? (dom-info-type info))) dom-infos))
  (define-values (mandatory-plain-dom-infos optional-plain-dom-infos)
    (partition dom-info-mandatory? plain-dom-infos))
  (define sorted-mandatory-plain-dom-infos (sort mandatory-plain-dom-infos < #:key dom-info-type))
  (define sorted-optional-plain-dom-infos (sort optional-plain-dom-infos < #:key dom-info-type))
  (define sorted-kw-dom-infos (sort kw-dom-infos keyword<? #:key dom-info-type))
  (with-lexical-env final-env
    (ret (-Con (make-Function
                (for/list ([vararg-slice-length (in-range (add1 (length optional-plain-dom-infos)))])
                 (make-arr*
                  (for/list ([dom (in-list (append sorted-mandatory-plain-dom-infos (take sorted-optional-plain-dom-infos vararg-slice-length)))])
                              (lookup-type/lexical (dom-info-id dom)))
                  (lookup-type/lexical rng-id)
                  #:rest #f
                  #:kws (for/list ([kw-dom (in-list sorted-kw-dom-infos)])
                          (define kw (dom-info-type kw-dom))
                          (define ty (lookup-type/lexical (dom-info-id kw-dom)))
                          (make-Keyword kw ty (dom-info-mandatory? kw-dom))))))))))

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
  (ret (-Con (for/fold ([ty Univ])
                       ([sub (in-list subs)])
               (define (can-refine-ty? s)
                 (and
                  ;; Knowing we have a Univ to the left of another contract
                  ;; doesn't give us any assumptions that we can use; e.g. it
                  ;; doesn't mean we can use an Integer->Bool function as a
                  ;; contract.
                  (not (type-equal? ty Univ))
                  ;; TODO: remove this case, it's a quick hack to handle the
                  ;; overlap between the functions we want to handle (T->Bool, T
                  ;; != Univ) and functions from Any->Bool that have a positive
                  ;; filter. The TODO below this, about considering using the
                  ;; meet of the type and the filter, would cover that overlap
                  ;; cleanly
                  (not (type-equal? s Univ))
                  ;; To use a s->Bool function as a contract in and/c, it has to
                  ;; come after a (Con ty) where ty <: s.
                  (subtype ty s)))
               (define domain-ty (tc-expr/t sub))
               (match domain-ty
                 [(Function: (list (arr: (list (? can-refine-ty? t)) (Values: (list (Result: -Boolean _ _))) _ _ _)))
                  ;; TODO: consider taking the meet of t and the positive filter
                  ;; If t is Integer and the filter says the true branch implies
                  ;; t is a Positive-Integer, then we should be able to use that
                  t]
                 [domain-ty (meet (get-core-type domain-ty) ty)])))))

;; tc-or/c : syntax -> (Con t)
(define (tc-or/c form)
  (define subs (sort (trawl-for-subs (ctc:or/c-sub-property form #f)
                                     (syntax-parser [:ctc:or/c^ #t]
                                                    [_ #f])
                                     ctc:or/c-sub-property)
                     <
                     #:key ctc:or/c-sub-property))
  (ret (-Con (for/fold ([ty (Un)])
                       ([sub (in-list subs)])
               (join (get-core-type (tc-expr/t sub)) ty)))))

;; check-contract : identifier syntax -> (void)
;; Errors iff the registered type of defn-id isn't compatible with the type of
;; the contract
(define (check-contract defn-id ctc)
  (define (filter->contract ty)
    (match ty
      [(PredicateFilter: (FilterSet: (TypeFilter: t _) fs-))
       #:when (subtype ty (-> Univ Univ))
       (-Con t)]
      ;; Can't use t -> Bool functions in place of filter'd functions because of
      ;; mutation. In CPCF they can permit this because there isn't mutation
      ;; Additionally, we'd have to require that t is a "base" type
      ;[(Function: (list (arr: t (== -Boolean) _ _ _))) (-Con t)]
      [_ ty]))
  (unless (compat? (lookup-type defn-id) (filter->contract (tc-expr/t ctc)))
    (tc-error/fields "contract is incompatible with type"
                     #:delayed? #t
                     "type" (lookup-type defn-id)
                     "contract type" (filter->contract (tc-expr/t ctc)))))
