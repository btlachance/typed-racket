#;
(exn-pred #rx"contract violation.*given: \"\"")
#lang typed/racket
(module server typed/racket
  (provide
   (contract-out
    [enhance ((or/c (not/c (string-len/c 1))
                    exact-integer?)
              . ->/c .
              any/c)]))
  (: enhance (-> (U String Integer) String))             
  (define (enhance artifact)
    (if (string? artifact)
        (string-append artifact artifact)
        (number->string (* 2 artifact)))))
(require 'server)
(enhance "")

