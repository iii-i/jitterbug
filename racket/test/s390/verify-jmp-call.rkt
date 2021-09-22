#lang racket/base

(require
  "../../lib/tests.rkt"
  (only-in "../../s390/spec.rkt" check-jit))

(module+ test
  (time (verify-jmp-call "s390-jmp-call tests" check-jit
                         #:selector (verify-only-in (list 'BPF_CALL 'BPF_EXIT)))))
