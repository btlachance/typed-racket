#lang racket/base
(require (except-in "../utils/utils.rkt"
                    in-sequence-forever)
         (for-syntax racket/base
                     racket/sequence
                     racket/syntax
                     racket/list
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
  [flat-named-contract (-poly (a b) (-> Univ (-FlatCon a b) (-FlatCon a b)))]
  [any/c (-FlatCon Univ Univ)]
  [none/c (-FlatCon Univ Univ)]
  [not/c (-poly (a b) (-> (-FlatCon a b) (-FlatCon a a)))]
  [=/c (cl->*
        (-> -Nat (-FlatCon Univ -Nat))
        (-> -Integer (-FlatCon Univ -Integer))
        (-> -Real (-FlatCon Univ -Real)))]
  [</c (-> -Real (-FlatCon Univ -Real))]
  [>/c (-> -Real (-FlatCon Univ -Real))]
  [<=/c (-> -Real (-FlatCon Univ -Real))]
  [>=/c (-> -Real (-FlatCon Univ -Real))]
  [between/c (-> -Real -Real (-FlatCon Univ -Real))]
  [real-in (-> -Real -Real (-FlatCon Univ -Real))]
  [integer-in (cl->*
               ;; using -Integer here because the second argument, unless we're
               ;; dealing with negative numbers, won't influence the type. This
               ;; way args like (-PosInt, -Integer) will still give us the
               ;; information that we want.
               (-> -PosInt -Integer (-FlatCon Univ -PosInt))
               (-> -Nat -Integer (-FlatCon Univ -Nat))
               (-> -Integer -Integer (-FlatCon Univ -Integer)))]
  [natural-number/c (-FlatCon Univ -Nat)]
  [string-len/c (-> -Real (-FlatCon Univ -String))]
  [false/c (-FlatCon Univ -False)]
  [printable/c (-FlatCon Univ Univ)]
  ;; one-of/c
  ;; vectorof
  ;; vector-immutableof (tricky, TR doesn't have immutable vectors)
  ;; vector/c
  ;; vector-immutable/c
  ;; box/c
  ;; box-immutable/c
  [listof (-poly (a b) (-> (-Con a b) (-Con (-lst a) (-lst b))))]
  [non-empty-listof (-poly (a b) (-> (-Con a b) (-Con (-lst a) (-pair b (-lst b)))))]
  [list*of (-poly (a b) (-> (-Con a b) (-Con (-mu x (-pair a (Un a x)))
                                             (-mu x (-pair b (Un b x))))))]
  [cons/c (-poly (a b c d) (-> (-Con a b) (-Con c d) (-Con Univ (-pair b d))))]
  ;; cons/dc
  [syntax/c (-poly (a b) (-> (-FlatCon a b) (-FlatCon (-Syntax a) (-Syntax b))))]
  ;; struct/c
  ;; struct/dc
  [parameter/c (-poly (a b c d) (cl->*
                                 (-> (-Con a b) (-Con (-Param b) (-Param b)))
                                 (-> (-Con a b) (-Con c d) (-Con (-Param b d)
                                                                 (-Param b d)))))]
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
  [symbols (->* (list) -Symbol (-Con Univ -Symbol))])

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

(define-syntax (list/c stx)
  (syntax-parse stx
    #:literals (list/c)
    [(list/c ctc:expr ...)
     (ctc:list/c
      #`(untyped:list/c #,@(for/list ([ctc (in-syntax #'(ctc ...))]
                                      [idx (in-naturals)])
                             (ctc:list/c-sub-property ctc idx))))]))

(define-syntax (->/c stx)
  (syntax-parse stx
    #:literals (->/c)
    [(->/c doms:expr ... rng:expr)
     (ctc:arrow (ignore #`(untyped:-> #,@(for/list ([dom (in-syntax #'(doms ...))]
                                                    [idx (in-naturals)])
                                           (ctc:arrow-dom-property dom idx))
                                      #,(ctc:arrow-rng #'rng))))]))

(define-syntax (->i stx)
  (define-syntax-class id+ctc
    #:attributes ((deps 1) id ctc)
    (pattern [id:id ctc]
             #:attr (deps 1) #f)
    (pattern [id:id (deps:id ...) ctc]))
  (define dom-counter 0)
  (define (next-dom-index)
    (begin0 dom-counter
      (set! dom-counter (add1 dom-counter))))
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
                                           (next-dom-index))
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
  ;; TODO: parameterized syntax class for streamlining pre/post conditions
  (define pre-counter 0)
  ;; pre-condition->forms : Syntax Syntax #:desc? [Option<Boolean>] #:name [Option<String>] -> Listof<(U Syntax Listof<Syntax>)>
  (define (pre-condition->forms deps condition #:desc? [desc? #f] #:name [name #f])
    (define kw
      (cond
        [desc? #'#:pre/desc]
        [name #'#:pre/name]
        [else #'#:pre]))
    (list kw
          deps
          (if name (list name) (list))
          (ctc:arrow-i-pre-property
           #`(let () #,@deps #,condition)
           (pre-info (syntax->list deps)
                     (begin0 pre-counter
                       (set! pre-counter (add1 pre-counter)))
                     desc?))))
  (define-splicing-syntax-class pre-condition
    #:attributes (forms)
    (pattern (~seq #:pre (deps:id ...) condition)
             #:attr forms
             (pre-condition->forms #'(deps ...) #'condition))
    (pattern (~seq #:pre/desc (deps:id ...) condition)
             #:attr forms
             (pre-condition->forms #'(deps ...) #'condition #:desc? #t))
    (pattern (~seq #:pre/name (deps:id ...) name:str condition)
             #:attr forms
             (pre-condition->forms #'(deps ...) #'condition #:name #'name)))
  (define post-counter 0)
  ;; post-condition->form : Syntax Syntax #:desc? [Option<Boolean>] #:name [Option<String>] -> Listof<(U Syntax Listof<Syntax>)>
  (define (post-condition->forms deps condition #:desc? [desc? #f] #:name [name #f])
    (define kw
      (cond
        [desc? #'#:post/desc]
        [name #'#:post/name]
        [else #'#:post]))
    (list kw
          deps
          (if name (list name) (list))
          (ctc:arrow-i-post-property
           ;; we use an empty let instead of a begin because the begin
           ;; was getting expanded away, making it much harder to
           ;; analyze the deps and condition as a single unit
           #`(let () #,@deps #,condition)
           (post-info (syntax->list deps)
                      (begin0 post-counter
                        (set! post-counter (add1 post-counter)))
                      desc?))))
  (define-splicing-syntax-class post-condition
    #:attributes (forms)
    (pattern (~seq #:post (deps:id ...) condition)
             #:attr forms
             (post-condition->forms #'(deps ...) #'condition))
    (pattern (~seq #:post/desc (deps:id ...) condition)
             #:attr forms
             (post-condition->forms #'(deps ...) #'condition #:desc? #t))
    (pattern (~seq #:post/name (deps:id ...) name:str condition)
             #:attr forms
             (post-condition->forms #'(deps ...) #'condition #:name #'name)))
    
  (define rng-counter 0)
  ;; MUTATES: modifies rng-counter
  (define (rng-id+ctc->form rng)
    (syntax-parse rng
      [rng:id+ctc
       (define index (+ rng-counter 1))
       (set! rng-counter index)
       (define info (rng-info #'rng.id (attribute rng.deps) #'rng.ctc index))
       (define new-ctc #`(begin #,@(or (attribute rng.deps) (list)) rng.ctc))
       #`[rng.id
          #,@(or (and (attribute rng.deps) (list (attribute rng.deps)))
                 (list))
          #,(ctc:arrow-i-rng-property new-ctc info)]]))
  (define-syntax-class dependent-range
    #:attributes (form)
    (pattern (~literal any)
             #:attr form
             (ctc:arrow-i-rng-property
              #'untyped:any
              (rng-info #f #f #'any 0)))
    (pattern ((~literal values) rng:id+ctc ...)
             #:attr form
             #`(values #,@(map rng-id+ctc->form (syntax->list #'(rng ...)))))
    ;; TODO: this overlaps with the (values id+ctc ...) case, so the order of
    ;; these matters -- fix that? is it cleaner to just note the order matters?
    (pattern rng:id+ctc
             #:attr form
             (rng-id+ctc->form #'rng)))
  (define-splicing-syntax-class dependent-rest
    #:attributes ((deps 1) ctc id)
    (pattern (~seq #:rest :id+ctc)))

  (syntax-parse stx
    #:literals (->i)
    [(->i ((~var mand-doms (dom #t)) ...)
          (~optional ((~var opt-doms (dom #f)) ...))
          (~optional rest:dependent-rest)
          (~optional (~seq pre:pre-condition ...))
          rng:dependent-range
          (~optional (~seq post:post-condition ...)))
     (ctc:arrow-i
      (ignore
       #`(untyped:->i (#,@(apply append (map syntax->list (or (attribute mand-doms.form)
                                                              (list)))))
                      (#,@(apply append (map syntax->list (or (attribute opt-doms.form)
                                                              (list)))))
                      #,@(if (attribute pre)
                             (flatten (attribute pre.forms))
                             (list))
                      #,@(if (attribute rest)
                             (list #'#:rest #`[rest.id
                                               #,@(or (and (attribute rest.deps) (list (attribute rest.deps)))
                                                      (list))
                                               #,(ctc:arrow-i-rest-property
                                                  #`(begin #,@(or (attribute rest.deps) (list))
                                                           rest.ctc)
                                                  (rest-info #'rest.id
                                                             (or (attribute rest.deps)
                                                                 (list))
                                                             #'rest.ctc))])
                             (list))
                      rng.form
                      #,@(if (attribute post)
                             (flatten (attribute post.forms))
                             (list)))))]))

