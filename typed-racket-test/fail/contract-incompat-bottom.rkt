#;
(exn-pred exn:fail:syntax? "contract is incompatible with type")
#lang typed/racket
(provide
 (contract-out
  [foo (->/c 5 5)]))
(define (foo x)
  x)
