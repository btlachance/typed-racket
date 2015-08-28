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

;; The make-variable-like-transformer'd bindings seem like they could just go in
;; base-env. The bummer there is that we still had to add any/c to the provides
;; for racket/base; just adding the any/c type didn't make it appear in the base
;; environment.

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

;; and/c requires us to calculate an intersection, so we can't give it a type
;; like the make-variable-... usages above
(define-syntax (and/c stx)
  (syntax-parse stx
    #:literals (and/c)
    [(and/c ctc:expr ...)
     (ctc:and/c
      #`(untyped:and/c #,@(for/list ([ctc (in-syntax #'(ctc ...))]
                                     [idx (in-naturals)])
                            (ctc:and/c-sub-property ctc idx))))]))

(define-syntax (->/c stx)
  (syntax-parse stx
    #:literals (->/c)
    [(->/c doms:expr ... rng:expr)
     (ctc:arrow #`(untyped:-> #,@(for/list ([dom (in-syntax #'(doms ...))]
                                            [idx (in-naturals)])
                                   (ctc:arrow-dom-property dom idx))
                              #,(ctc:arrow-rng #'rng)))]))
