(define f (lambda (x) (lambda (y) x)))
(define g (f 2))
(g 3)