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
                     (utils contract-utils)
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
  [not/c (-poly (a) (-> (-FlatCon a) (-FlatCon Univ)))]
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
             #:attr (deps 1) #f)
    (pattern [id:id (deps:id ...) ctc]))
  (define dom-counter 0)
  (define-splicing-syntax-class (dom mandatory?)
    #:attributes (form)
    (pattern (~seq (~optional kw:keyword) dom:id+ctc)
             #:attr form (begin
                           (define info
                             (dom-info #'dom.id
                                       (attribute dom.deps)
                                       #'dom.ctc
                                       (if (attribute kw)
                                           (syntax-e (attribute kw))
                                           (begin0 dom-counter
                                             (set! dom-counter (add1 dom-counter))))
                                       mandatory?))
                           (define deps-to-splice (if (dom-info-deps info)
                                                      (list (dom-info-deps info))
                                                      (list)))
                           (define kw-to-splice (if (keyword? (dom-info-type info))
                                                    (list (dom-info-type info))
                                                    (list)))
                           #`(#,@kw-to-splice
                              (dom.id
                               #,@deps-to-splice
                               #,(ctc:arrow-i-dom-property
                                  ;; ->i doesn't preserve the syntax properties if we
                                  ;; put this on the id+ctc pair; it also doesn't
                                  ;; guarantee that the identifier for the named dom
                                  ;; position will end up in the expanded syntax. The
                                  ;; ctc is most likely to be in the expansion, so
                                  ;; we'll put all the properties there
                                  #`(begin #,@(or (attribute dom.deps) (list)) dom.ctc)
                                  info))))))
  (define-syntax-class dependent-range
    #:attributes ((deps 1) ctc id)
    (pattern (~literal any)
             #:attr (deps 1) #f
             #:attr ctc #'any
             #:attr id #'_)
    (pattern :id+ctc))

  (syntax-parse stx
    #:literals (->i)
    [(->i ((~var mand-doms (dom #t)) ...)
          (~optional ((~var opt-doms (dom #f)) ...))
          rng:dependent-range)
     (ctc:arrow-i
      (ignore
       #`(untyped:->i (#,@(apply append (map syntax->list (or (attribute mand-doms.form)
                                                              (list)))))
                      (#,@(apply append (map syntax->list (or (attribute opt-doms.form)
                                                              (list)))))
                      (rng.id
                       #,@(or (and (attribute rng.deps) (list (attribute rng.deps)))
                              (list))
                       #,(ctc:arrow-i-rng-property
                          #`(begin #,@(or (attribute rng.deps) (list))
                                   rng.ctc)
                          (rng-info #'rng.id
                                    (or (attribute rng.deps)
                                        (list))
                                    #'rng.ctc
                                    0))))))]))

