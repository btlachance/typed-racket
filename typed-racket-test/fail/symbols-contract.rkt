#;
(exn-pred #rx"broke its own contract.*curlyville")
#lang racket
(module server typed/racket
  (provide
   (contract-out
    [famous-cities (listof (symbols 'paris 'london '|new york|))]))
  (define famous-cities (list 'london 'curlyville)))
(require 'server)
famous-cities
