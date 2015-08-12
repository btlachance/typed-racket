#lang racket/base
(require "../utils/utils.rkt"
         syntax/parse
         racket/match
         (utils tc-utils)
         (env global-env)
         (rep type-rep)
         (types subtype numeric-tower base-abbrev)
         (prefix-in c: racket/contract))
(provide tc-contract
         contract-type)

(define-literal-set contract-literals
  (c:any/c string? integer? number? real? c:>/c c:</c c:->))
;; syntax -> Type
(define (contract-type ctc)
  (syntax-parse ctc
    #:literal-sets (contract-literals)
    [c:any/c Univ]
    [string? -String]
    [integer? -Integer]
    [number? -Number]
    [real? -Real]
    [(c:>/c _) -Real]
    [(c:</c _) -Real]
    [(c:-> args ... ret)
     (->* (map contract-type (syntax->list #'(args ...)))
          (contract-type #'ret))]))
(module+ test
  (require rackunit)
  (check-equal? (contract-type #'c:any/c) Univ)
  (check-equal? (contract-type #'(c:>/c 100)) -Real)
  (check-equal? (contract-type #'(c:-> c:any/c number? string?))
                (->* (list Univ -Number) -String)))

;; compat? : Type Type -> Boolean
(define (compat? id-type ctc-type)
  (match* (id-type ctc-type)
    [((Function: (list (arr: s1 s2 _ _ _)))
      (Function: (list (arr: t1 t2 _ _ _))))
     (and (andmap compat? s1 t1)
          (compat? s2 t2))]
    [(s t)
     ;; equal? maybe not necessary, we check subtype in both directions
     (or (equal? s t) (subtype s t) (subtype t s))]))
(module+ test
  (check-true (compat? -Real -Integer))
  (check-true (compat? -Integer -Real))
  (check-true (compat? (->* (list -Integer) -Integer)
                       (->* (list -Real) -Real)))
  (check-true (compat? (->* (list -Integer) -Integer)
                       (->* (list Univ) -Real))))

;; tc-contract : identifier? syntax -> (void)
;; Errors iff the registered type of defn-id isn't compatible with the type of
;; the contract
(define (tc-contract defn-id ctc)
  (unless (compat? (lookup-type defn-id) (contract-type ctc))
    (tc-error/fields "contract is incompatible with type"
                     #:delayed? #t
                     #:stx ctc
                     "type" (lookup-type defn-id)
                     "contract type" (contract-type ctc))))
