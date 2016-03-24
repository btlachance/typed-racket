#lang typed/racket
;; checks that a contract can go from typed->typed then be used as a contract
(module server typed/racket
  (provide (contract-out [pizza-order/c any/c]))
  (define pizza-order/c (->/c (integer-in 12 20)
                              (or/c 'small 'medium 'large)
                              any/c)))
(module store typed/racket
  (require (submod ".." server))
  (provide
   (contract-out
    [order-pizza pizza-order/c]))
  (: order-pizza (-> Integer (U 'small 'medium 'large) Boolean))
  (define (order-pizza price size)
    #t))
