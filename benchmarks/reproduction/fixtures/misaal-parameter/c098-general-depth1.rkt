
        #lang rosette
        (require rosette/lib/synthax)
        (require rosette/lib/angelic)
        (require racket/pretty)
        (require rosette/lib/destruct)
        (require hydride)
        (require misaal)
        (require rosette/solver/smt/boolector)
        (require rosette/solver/smt/z3)

        ;; Uncomment the line below to enable verbose logging
        (enable-debug)
        (custodian-limit-memory (current-custodian) (* 10000 1024 1024))
        (current-bitwidth 16)
        
(define param-test-cases (list 
(TESTS 2 (vector 1 5))
(TESTS 4 (vector 2 7))
(TESTS 6 (vector 3 11))
))
(define-values (sat? expr) (synthesize-param-expression param-test-cases 1 1 (list 1)))
(cond
[sat? (write-str-to-file (~v expr) "general-depth1.temp") (exit 0)]
[else (exit 1)]
)
