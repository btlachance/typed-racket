#lang racket/unit
(require racket/match
         syntax/parse
         "../utils/utils.rkt"
         (env global-env)
         (types subtype abbrev tc-result match-expanders union)
         (only-in (infer infer)
                  meet join)
         (utils tc-utils)
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
  (match ty
    [(PredicateFilter: (FilterSet: (TypeFilter: t _) fs-)) t]
    [(Con*: t) t]
    ;; See explanation in filter->contract
    ;[(Function: (list (arr: t (== -Boolean) _ _ _))) t]
    [_ (Un)]))

;; trawl-for-doms/rng : syntax (any/c -> any/c) -> (listof syntax)
;; Finds syntax/subforms for which is-dom/rng? returns a non-#f value. Does not
;; recur into arrow subforms since those must still be typechecked. Do not call
;; with an arrow that is also a domain/range, that will infinite loop.
(define (trawl-for-doms/rng form is-dom/rng?)
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
           [:ctc:arrow^
            ;; we only want arrows that match the predicate; e.g. when looking
            ;; for the rng we have to make sure we don't grab a dom
            #:when (is-dom/rng? form)
            (values (cons form arrows) non-arrows)]
           [:ctc:arrow^
            (values arrows non-arrows)]
           [_ (values arrows (cons form non-arrows))])))
     (for/fold ([doms/rng arrows])
               ([non-arrow (in-list non-arrows)])
       (append doms/rng (trawl-for-doms/rng non-arrow is-dom/rng?)))]
    [_ '()]))

;; tc-arrow-contract : syntax -> (Con t)
(define (tc-arrow-contract form)
  (define cleaned-arrow
    (syntax-property (syntax-property form 'ctc:arrow-rng #f)
                     'ctc:arrow-dom
                     #f))
  (define doms
    (sort (trawl-for-doms/rng cleaned-arrow ctc:arrow-dom-property)
          <
          #:key ctc:arrow-dom-property))
  (define rng
    (car (trawl-for-doms/rng cleaned-arrow
                             (syntax-parser
                               [:ctc:arrow-rng^ #t]
                               [_ #f]))))
  (ret (-Con (->* (for/list ([dom (in-list doms)])
                    (get-core-type (tc-expr/t dom)))
                  (get-core-type (tc-expr/t rng))))))

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
               (meet (get-core-type (tc-expr/t sub)) ty)))))

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
      [(PredicateFilter: (FilterSet: (TypeFilter: t _) fs-)) (-Con t)]
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