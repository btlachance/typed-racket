#lang racket/base
(require (except-in "../utils/utils.rkt"
                    in-sequence-forever)
         (for-syntax racket/base
                     racket/sequence
                     racket/syntax
                     syntax/parse
                     syntax/transformer
                     (types abbrev numeric-tower union)
                     (rep type-rep)
                     (private syntax-properties))
         (prefix-in untyped: racket/contract/base))
(provide (except-out (all-defined-out)
                     define-contract))

(define-syntax (define-contract stx)
  (define-syntax-class def
    (pattern [ctc:identifier ty]
             #:with untyped-ctc (format-id stx "untyped:~a" #'ctc)))
  (syntax-parse stx
    [(_  :def ...)
     #'(begin
         (define-syntax ctc
           (make-variable-like-transformer
            (assume-type-property #'untyped-ctc ty))) ...)]))

(define-contract
  [flat-named-contract (-poly (a) (-> Univ (-FlatCon a) (-FlatCon a)))]
  [any/c (-FlatCon Univ)]
  [none/c (-FlatCon Univ)]
  [not/c (-poly (a) (-> (-FlatCon a) (-FlatCon a)))]
  [=/c (-> -Real (-FlatCon -Real))]
  [</c (-> -Real (-FlatCon -Real))]
  [>/c (-> -Real (-FlatCon -Real))]
  [<=/c (-> -Real (-FlatCon -Real))]
  [>=/c (-> -Real (-FlatCon -Real))]
  [between/c (-> -Real -Real (-FlatCon -Real))]
  [real-in (-> -Real -Real (-FlatCon -Real))]
  [integer-in (-> -Integer -Integer (-FlatCon -Integer))]
  [natural-number/c (-FlatCon -Nat)]
  [string-len/c (-> -Real (-FlatCon -String))]
  [false/c (-FlatCon -False)]
  [printable/c (-FlatCon Univ)]
  ;; one-of/c
  ;; vectorof
  ;; vector-immutableof (tricky, TR doesn't have immutable vectors)
  ;; vector/c
  ;; vector-immutable/c
  ;; box/c
  ;; box-immutable/c
  [listof (-poly (a) (-> (-Con a) (-Con (-lst a))))]
  [non-empty-listof (-poly (a) (-> (-Con a) (-Con (-lst a))))]
  [list*of (-poly (a) (-> (-Con a) (-Con (-mu x (-pair a (Un a x))))))]
  [cons/c (-poly (a b) (-> (-Con a) (-Con b) (-Con (-pair a b))))]
  ;; cons/dc
  [list/c (-polydots (a) (->... (list) ((-Con a) a) (-Con (make-ListDots a 'a))))]
  [syntax/c (-poly (a) (-> (-FlatCon a) (-FlatCon (-Syntax a))))]
  ;; struct/c
  ;; struct/dc
  ;; parameter/c
  ;; procedure-arity-includes/c
  ;; hash/c
  ;; hash/dc
  ;; channel/c
  ;; prompt-tag/c
  ;; continuation-mark-key/c
  ;; evt/c
  ;; flat-rec-contract
  ;; flat-murec-contract
  ;; any
  ;; promise/c
  ;; flat-contract
  ;; flat-contract-predicate
  [symbols (->* (list) -Symbol (-Con -Symbol))])

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

(define-syntax (or/c stx)
  (syntax-parse stx
    #:literals (or/c)
    [(or/c ctc:expr ...)
     (ctc:or/c
      #`(untyped:or/c #,@(for/list ([ctc (in-syntax #'(ctc ...))]
                                    [idx (in-naturals)])
                           (ctc:or/c-sub-property ctc idx))))]))

(define-syntax (->/c stx)
  (syntax-parse stx
    #:literals (->/c)
    [(->/c doms:expr ... rng:expr)
     (ctc:arrow #`(untyped:-> #,@(for/list ([dom (in-syntax #'(doms ...))]
                                            [idx (in-naturals)])
                                   (ctc:arrow-dom-property dom idx))
                              #,(ctc:arrow-rng #'rng)))]))

(define-syntax (->i stx)
  (define-syntax-class id+ctc
    #:attributes ((deps 1) id ctc)
    (pattern [id:id ctc]
             #:attr (deps 1) '())
    (pattern [id:id (deps:id ...) ctc]))
  #;(define-splicing-syntax-class dependent-rest
  (pattern (~seq #:rest :id+ctc)))
  #;(define-splicing-syntax-class pre-condition
  (pattern (~seq #:pre (id:id ...) pre-test)))
  #;(define-splicing-syntax-class post-condition
  (pattern (~seq #:post (id:id ...) post-test)))
  (define-syntax-class dependent-range
    #:attributes ((deps 1) ctc id)
    (pattern (~literal any)
             #:attr (deps 1) '()
             #:attr ctc #'any
             #:attr id #'_)
    (pattern :id+ctc))

  (syntax-parse stx
    #:literals (->i)
    [(->i (doms:id+ctc ...)
          rng:dependent-range)
     (ctc:arrow-i
      (ignore
       #`(untyped:->i (#,@(for/list ([dom (in-syntax #'(doms ...))]
                                     [ctc (in-syntax #'(doms.ctc ...))]
                                     [name (in-syntax #'(doms.id ...))]
                                     [deps (in-syntax #'((doms.deps ...) ...))]
                                     [index (in-naturals)])
                            ;; ->i doesn't preserve the syntax properties if we
                            ;; put this on the id+ctc pair; it also doesn't
                            ;; guarantee that the identifier for the named dom
                            ;; position will end up in the expanded syntax. The
                            ;; ctc is most likely to be in the expansion, so
                            ;; we'll put all the properties there
                            #`(#,name
                               #,@(if (> (length (syntax->list deps)) 0)
                                      (list deps)
                                      (list))
                               #,(ctc:arrow-i-dom-property
                                  #`(begin #,@deps #,ctc)
                                  (list index name ctc (syntax->list deps))))))
                      (rng.id
                       #,@(if (> (length (syntax->list #'(rng.deps ...))) 0)
                              #'((rng.deps ...))
                              #'())
                       #,(ctc:arrow-i-rng-property
                          #'(begin rng.deps ... rng.ctc)
                          (list #'rng.id #'rng.ctc (syntax->list #'(rng.deps ...))))))))]))

