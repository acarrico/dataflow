#lang racket

(module+ test (require rackunit))

(require racket/generic)

(provide constant input output lift event propagate previous)

(define-generics signal
  (signal-rank signal))

(define-generics source
  (source-value source)
  (source-add-sink source sink))

(define-generics sink
  (sink-stale sink)
  (sink-update sink))

(define (add-sink boxed-sinks sink)
  (set-box! boxed-sinks (cons (make-weak-box sink) (unbox boxed-sinks))))

(define (queue-sinks boxed-sinks)
  (for-each
   (lambda (weak-boxed-sink)
     (let ((sink (weak-box-value weak-boxed-sink)))
       ;; NOTE: The sink might have been garbage collected.
       ;; ISSUE: should get rid of the links to gc-ed sinks.
       (when (sink? sink) (sink-stale sink))))
   (unbox boxed-sinks)))

(define constant-rank 0)
(define input-rank 1)

(struct constant (value)
        #:methods gen:signal
        ((define (signal-rank signal) constant-rank))
        #:methods gen:source
        ((define (source-value source) (constant-value source))
         (define (source-add-sink source sink) (void))))

(struct input-rep (boxed-value boxed-sinks)
        #:methods gen:signal
        ((define (signal-rank signal) input-rank))
        #:methods gen:source
        ((define (source-value source) (unbox (input-boxed-value source)))
         (define (source-add-sink source sink)
           (add-sink (input-boxed-sinks source) sink))))

(define input-boxed-value input-rep-boxed-value)
(define input-boxed-sinks input-rep-boxed-sinks)

(define (input initial-value)
  (input-rep (box initial-value) (box '())))

(define (event i val)
  (set-box! (input-boxed-value i) val)
  (queue-sinks (input-boxed-sinks i))
  (void))

(struct output-rep (source callback boxed-stale?)
        #:methods gen:signal
        ((define/generic generic-signal-rank signal-rank)
         (define (signal-rank signal)
           (+ 1 (generic-signal-rank (output-source signal)))))
        #:methods gen:sink
        ((define (sink-stale sink)
           (queue-update (output-boxed-stale? sink) sink))
         (define (sink-update sink)
           (set-box! (output-boxed-stale? sink) #f)
           ((output-callback sink) (source-value (output-source sink))))))

(define output-source output-rep-source)
(define output-callback output-rep-callback)
(define output-boxed-stale? output-rep-boxed-stale?)

(define (output source callback)
  (define o (output-rep source callback (box #f)))
  (source-add-sink source o)
  o)

(struct fn (rank boxed-value boxed-sinks snap boxed-stale?)
        #:methods gen:signal
        ((define (signal-rank signal) (fn-rank signal)))
        #:methods gen:source
        ((define (source-value source) (unbox (fn-boxed-value source)))
         (define (source-add-sink source sink)
           (add-sink (fn-boxed-sinks source) sink)))
        #:methods gen:sink
        ((define (sink-stale sink)
           (queue-update (fn-boxed-stale? sink) sink))
         (define (sink-update sink)
           (set-box! (fn-boxed-stale? sink) #f)
           (set-box! (fn-boxed-value sink) ((fn-snap sink)))
           (queue-sinks (fn-boxed-sinks sink))
           (void))
         ))

(define-struct
  lift
  (fn)
  #:property prop:procedure
  (lambda (self . args)
    (for-each (lambda (arg)
                (unless (source? arg) (error "lift: argument is not a source")))
              args)
    (let* ((max-arg-rank (foldl (lambda (sig rank) (max rank (signal-rank sig)))
                                constant-rank
                                args))
           (op (lift-fn self))
           (snap (lambda () (apply op (map source-value args))))
           (initial-value (snap)))
      (if (= max-arg-rank constant-rank)
          ;; constant source:
          (constant initial-value)
          ;; not constant source:
          (let ((f (fn (+ max-arg-rank 1) (box initial-value) (box '()) snap (box #f))))
            (for-each (lambda (arg) (source-add-sink arg f)) args)
            f)))))

;; A time step corresponds to an event propagation (or the propagation
;; of simultanious events).
;;
;; The 'prev' operator:
;;
;; IEEE
;; 01234 x2 :=
;; 00123 x1 := (prev x2 0)
;; 00012 x0 := (prev x1 0)
;; 01369 y := ((lift +) x0 x1 x2)
;;
;; In this version, (prev x), (prev (prev x)), etc. have increasing
;; ranks.

;; NOTE: This version wastes some space, recording the current value
;; of the source. This cache allows the previous node to update after
;; its source. It could be eliminated by arranging for previous
;; operators to update just before their sources.
(struct previous-rep (source boxed-current-value boxed-value boxed-sinks boxed-stale?)
        #:methods gen:signal
        ((define/generic generic-signal-rank signal-rank)
         (define (signal-rank signal) (+ 1 (generic-signal-rank (previous-source signal)))))
        #:methods gen:source
        ((define (source-value source) (unbox (previous-boxed-value source)))
         (define (source-add-sink source sink) (add-sink (previous-boxed-sinks source) sink)))
        #:methods gen:sink
        ((define (sink-stale sink)
           (queue-update (previous-boxed-stale? sink) sink)
           ;; queue sinks right away.
           (queue-sinks (previous-boxed-sinks sink)))
         (define (sink-update sink)
           (set-box! (previous-boxed-stale? sink) #f)
           (set-box! (previous-boxed-value sink) (unbox (previous-boxed-current-value sink)))
           (set-box! (previous-boxed-current-value sink) (source-value (previous-source sink))))
         ))

(define previous-source previous-rep-source)
(define previous-boxed-current-value previous-rep-boxed-current-value)
(define previous-boxed-value previous-rep-boxed-value)
(define previous-boxed-sinks previous-rep-boxed-sinks)
(define previous-boxed-stale? previous-rep-boxed-stale?)

(define (previous source initial-value)
  (if (= constant-rank (signal-rank source))
      (constant initial-value)
      (let ((p  (previous-rep source (box (source-value source))
                              (box initial-value) (box '()) (box #f))))
        (source-add-sink source p)
        p)))

(require persistent/measured-fingertree-sig)
(require persistent/measured-fingertree-unit)
(require persistent/measured-sig)

(define rank-min
  (lambda (x y)
    (min x y)))

;; ISSUE: should really use a flag, but this ought to be pretty safe:
(define mzero-rank 99999)

(define-values/invoke-unit
  measured-fingertree@
  (import (rename measured^
                  (rank-min mplus)
                  (mzero-rank  mzero)
                  (signal-rank measure)))
  (export measured-fingertree^))

(define stale-nodes (fingertree))

(define (queue-update boxed-stale? sink)
  (unless (unbox boxed-stale?)
          ;; !!! ISSUE: should be queueing the sink in its weak box !!!
          ;; this is mentioned in the frtime thesis section 2.6.1.
          (set! stale-nodes (push-left sink stale-nodes))
          (set-box! boxed-stale? #t)))

(define (propagate)
  (let loop ()
    (unless (empty? stale-nodes)
      (split (let ((rank (measure stale-nodes))) (lambda (r) (= r rank)))
             mzero-rank
             stale-nodes
             (lambda (left sig right)
               (set! stale-nodes (concatenate left right))
               (sink-update sig)
               (loop))
             (lambda (pq)
               (error "propagate: Shouldn't be here." pq)))))
  )

(module+
 test

 (check = 3 (source-value ((lift +) (constant 1) (constant 2))))

 (let* ((x (input 0))
        (y (output x (lambda (value) (printf "hello world\n") (check = value 1)))))
   (check = 1 (signal-rank x))
   (check = 2 (signal-rank y))
   (check eq? (weak-box-value (car (unbox (input-rep-boxed-sinks x)))) y)
   (event x 1)
   (propagate))

 (let* ((x1 (input 0))
        (x2 (input 0))
        (y ((lift +) x1 x2)))
   (check = 0 (source-value y))
   (event x1 7)
   (event x2 9)
   (propagate)
   (check = 7 (source-value x1))
   (check = 9 (source-value x2))
   (check = 16 (source-value y)))

 (let* ((x1 (input 1))
        (x0 (previous x1 1))
        (y ((lift +) x0 x1)))
   ;; 1 + 1
   (check = 2 (source-value y))

   ;; 2 + 1
   (event x1 2)
   (propagate)
   (check = 3 (source-value y))

   ;; 2 + 3
   (event x1 3)
   (propagate)
   (check = 5 (source-value y)))

 (let* ((x2 (input 1))
        (x1 (previous x2 0))
        (x0 (previous x1 0))
        (y ((lift +) ((lift +) x0 x1) x2)))
   ;; 0, 0, 1
   (check = 1 (source-value y))
   (printf "::: ~s\n" (map source-value (list y x0 x1 x2)))
   ;; 0, 1, 2
   (event x2 2)
   (propagate)
   (printf "::: ~s\n" (map source-value (list y x0 x1 x2)))
   (check = 3 (source-value y))

   ;; 1, 2, 3
   (event x2 3)
   (propagate)
   (printf "::: ~s\n" (map source-value (list y x0 x1 x2)))
   (check = 6 (source-value y))

   ;; 2, 3, 4
   (event x2 4)
   (propagate)
   (printf "::: ~s\n" (map source-value (list y x0 x1 x2)))
   (check = 9 (source-value y)))
 )
