#lang typed/racket
(provide
 (contract-out
  [add1 (->/c exact-integer? exact-integer?)]))

(: add1 (-> Integer Integer))
(define (add1 x)
  (+ 1 x))
