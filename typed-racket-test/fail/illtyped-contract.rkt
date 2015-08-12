#;
(exn-pred exn:fail:contract? "contract type.*is incompatible with type")
#lang typed/racket
(provide
 (contract-out
  [doubler (->/c string? string?)]))

(: doubler : Integer -> Integer)
(define (doubler x)
  (+ x x))