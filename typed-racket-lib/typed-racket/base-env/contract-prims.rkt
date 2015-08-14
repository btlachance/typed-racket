#lang racket/base
(require (except-in "../utils/utils.rkt"
                    in-sequence-forever)
         (for-syntax racket/base
                     racket/sequence
                     syntax/parse
                     syntax/transformer
                     (types abbrev numeric-tower)
                     (rep type-rep)
                     (private syntax-properties))
         (prefix-in untyped: racket/contract/base))
(provide (all-defined-out))

(define-syntax any/c
  (make-variable-like-transformer
   (assume-type-property #'untyped:any/c (make-Con Univ))))

(define-syntax string-len/c
  (make-variable-like-transformer
   (assume-type-property #'untyped:string-len/c (-> -Real (make-Con -String)))))

(define-syntax >/c
  (make-variable-like-transformer
   (assume-type-property #'untyped:>/c (-> -Real (make-Con -Real)))))

(define-syntax </c
  (make-variable-like-transformer
   (assume-type-property #'untyped:</c (-> -Real (make-Con -Real)))))

(define-syntax (->/c stx)
  (syntax-parse stx
    #:literals (->/c)
    [(->/c doms:expr ... rng:expr)
     (ctc:arrow #`(untyped:-> #,@(for/list ([dom (in-syntax #'(doms ...))]
                                            [idx (in-naturals)])
                                   (ctc:arrow-dom-property dom idx))
                              #,(ctc:arrow-rng #'rng)))]))
