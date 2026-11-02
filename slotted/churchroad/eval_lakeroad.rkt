#lang racket/base
;; Observe Rosette's existing solver events without changing the synthesis query.
;; solve spans check-sat and model reading; encode includes solver startup.
(require json racket/vector rosette/base/core/reporter)

(define args (current-command-line-arguments))
(define target (string->path (vector-ref args 0)))
(current-command-line-arguments (vector-drop args 1))
(define starts (make-hash))
(define (now) (/ (current-inexact-monotonic-milliseconds) 1000.0))
(define (record phase)
  (define elapsed (- (now) (hash-ref starts phase)))
  (call-with-output-file (getenv "CHURCHROAD_EVAL_ROSETTE_EVENTS")
    (lambda (out)
      (write-json (hash 'phase phase 'seconds elapsed) out)
      (newline out))
    #:exists 'append))
(define previous (current-reporter))
(current-reporter
 (lambda (event . data)
   (case event
     [(solve-start) (hash-set! starts "solve" (now))]
     [(solve-finish) (record "solve")]
     [(encode-start) (hash-set! starts "encode" (now))]
     [(encode-finish) (record "encode")])
   (apply previous event data)))
(dynamic-require target #f)
