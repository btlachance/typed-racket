#lang racket
(module gt-5-pro typed/racket
  (provide (contract-out
            [gt-5 (>/c 5)]))
  (: gt-5 Integer)
  (define gt-5 6))
(require 'gt-5-pro)
gt-5
