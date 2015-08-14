#lang racket/base
(require "../utils/utils.rkt"
         syntax/parse
         racket/match
         (utils tc-utils)
         (env global-env)
         (base-env contract-prims)
         (rep type-rep filter-rep)
         (typecheck typechecker)
         (types subtype numeric-tower abbrev tc-result match-expanders union)
         (prefix-in c: racket/contract))
(module+ test
  (require rackunit))
(provide check-contract)

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
(module+ test
  (check-true (compat? -Real (-Con -Integer)))
  (check-true (compat? -Integer (-Con -Real)))
  (check-true (compat? (->* (list -Integer) -Integer)
                       (-Con (->* (list -Real) -Real))))
  (check-true (compat? (->* (list -Integer) -Integer)
                       (-Con (->* (list Univ) -Real))))
  (check-true (compat? (->* (list -Integer) Univ)
                       (-Con (->* (list Univ) -Integer))))
  (check-false (compat? (Un) (-Con -String))))

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
