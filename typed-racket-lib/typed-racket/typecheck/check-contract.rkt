#lang racket/unit
(require racket/match
         syntax/parse
         "../utils/utils.rkt"
         (env global-env)
         (types subtype abbrev tc-result match-expanders union)
         (utils tc-utils)
         (rep type-rep filter-rep)
         (private syntax-properties)
         "signatures.rkt")

(import tc-expr^)
(export check-contract^)

;; compat? : Type Type -> Boolean
(define (compat? id-type ctc-type)
  (match* (id-type ctc-type)
    [(_
      (Con: (== Univ)))
      #t]
    [((Function: (list (arr: s1s s2 _ _ _)))
      (Con: (Function: (list (arr: t1s t2 _ _ _)))))
     (and (andmap compat? s1s t1s)
          (compat? s2 t2))]
    ;; Because we check subtype in both directions, have to explicitly disallow this
    [(s (Con: t))
     #:when (or (equal? s (Un)) (equal? t (Un)))
     #f]
    [(s (or (Con: t) t))
     ;; equal? maybe not necessary, we check subtype in both directions
     (or (equal? s t) (subtype s t) (subtype t s))]
    [(_ _) #f]))

;; TODO: Use this for check-contract, too. Something like:
;; (-Con (get-core-type t))
(define (get-core-type ty)
  (match ty
    [(PredicateFilter: (FilterSet: (TypeFilter: t _) fs-)) t]
    [(Con: t) t]
    [_ (Un)]))

;; trawl-for : syntax (any/c -> any/c) -> (list syntax)
;; Finds syntaxes that are form/its subforms for which accessor returns a non-#f
;; value. Very similar to the trawl-for-property in check-class-unit
(define (trawl-for form accessor)
  (syntax-parse form
    [stx
     #:when (accessor #'stx)
     (list #'stx)]
    [(forms ...)
     (apply append (map (lambda (form) (trawl-for form accessor))
                        (syntax->list #'(forms ...))))]
    [_ '()]))

;; tc-arrow-contract : syntax -> (Con t)
(define (tc-arrow-contract form)
  (define doms
    (sort (trawl-for form ctc:arrow-dom-property)
          <
          #:key ctc:arrow-dom-property))
  (define rng
    (car (trawl-for form (syntax-parser
                           [:ctc:arrow-rng^ #t]
                           [_ #f]))))
  (define doms-tys (for/list ([dom (in-list doms)])
                     (get-core-type (tc-expr/t dom))))
  (define rng-ty (get-core-type (tc-expr/t rng)))
  (ret (-Con (->* doms-tys rng-ty))))

;; check-contract : identifier syntax -> (void)
;; Errors iff the registered type of defn-id isn't compatible with the type of
;; the contract
(define (check-contract defn-id ctc)
  (define (filter->contract ty)
    (match ty
      [(PredicateFilter: (FilterSet: (TypeFilter: t _) fs-)) (-Con t)]
      [_ ty]))
  (unless (compat? (lookup-type defn-id) (filter->contract (tc-expr/t ctc)))
    (tc-error/fields "contract is incompatible with type"
                     #:delayed? #t
                     "type" (lookup-type defn-id)
                     "contract type" (filter->contract (tc-expr/t ctc)))))
