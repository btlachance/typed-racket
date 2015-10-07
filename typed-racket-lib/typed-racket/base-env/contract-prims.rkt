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
   (assume-type-property #'untyped:any/c (-FlatCon Univ))))

(define-syntax string-len/c
  (make-variable-like-transformer
   (assume-type-property #'untyped:string-len/c (-> -Real (-FlatCon -String)))))

(define-syntax >/c
  (make-variable-like-transformer
   (assume-type-property #'untyped:>/c (-> -Real (-FlatCon -Real)))))

(define-syntax </c
  (make-variable-like-transformer
   (assume-type-property #'untyped:</c (-> -Real (-FlatCon -Real)))))

(define-syntax =/c
  (make-variable-like-transformer
   (assume-type-property #'untyped:=/c (-> -Real (-FlatCon -Real)))))

(define-syntax <=/c
  (make-variable-like-transformer
   (assume-type-property #'untyped:<=/c (-> -Real (-FlatCon -Real)))))

(define-syntax >=/c
  (make-variable-like-transformer
   (assume-type-property #'untyped:>=/c (-> -Real (-FlatCon -Real)))))

(define-syntax between/c
  (make-variable-like-transformer
   (assume-type-property #'untyped:between/c (-> -Real -Real (-FlatCon -Real)))))

(define-syntax real-in
  (make-variable-like-transformer
   (assume-type-property #'untyped:real-in (-> -Real -Real (-FlatCon -Real)))))

(define-syntax integer-in
  (make-variable-like-transformer
   (assume-type-property #'untyped:integer-in (-> -Integer -Integer (-FlatCon -Integer)))))

(define-syntax false/c
  (make-variable-like-transformer
   (assume-type-property #'untyped:false/c (-FlatCon -False))))

(define-syntax listof
  (make-variable-like-transformer
   (assume-type-property #'untyped:listof (-poly (a) (-> (-Con a) (-Con (-lst a)))))))

(define-syntax non-empty-listof
  (make-variable-like-transformer
   (assume-type-property #'untyped:non-empty-listof (-poly (a) (-> (-Con a) (-Con (-lst a)))))))

(define-syntax list/c
  (make-variable-like-transformer
   (assume-type-property #'untyped:list/c (-polydots (a) (->... (list) ((-Con a) a) (-Con (make-ListDots a 'a)))))))

;; Need type distinction distinguish between flat and non-flat contracts; o/wise
;; this can't be supported without runtime errors.
(define-syntax flat-named-contract
  (make-variable-like-transformer
   (assume-type-property #'untyped:flat-named-contract
                         (-poly (a) (-> Univ (-FlatCon a) (-FlatCon a))))))

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
