#;
(exn-pred exn:fail:syntax? "contract is incompatible with type")
#lang typed/racket
(provide
 (contract-out
  [doubler (->/c string? string?)]))

(: doubler : Integer -> Integer)
(define (doubler x)
  (+ x x))
