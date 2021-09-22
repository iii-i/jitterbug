#lang racket/base

(require
  "../../lib/tests.rkt"
  (only-in "../../s390/spec.rkt" check-jit))

(module+ test
  (time (verify-alu32-x "s390-alu32-x tests" check-jit)))
