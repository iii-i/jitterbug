#lang racket/base

(require
  "../../lib/tests.rkt"
  (only-in "../../s390/spec.rkt" check-jit))

(module+ test
  (time (verify-jmp64-x "s390-jmp64-x tests" check-jit)))
