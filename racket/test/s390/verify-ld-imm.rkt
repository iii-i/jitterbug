#lang racket/base

(require
  "../../lib/tests.rkt"
  (only-in "../../s390/spec.rkt" check-jit))

(module+ test
  (time (verify-ld-imm "s390-ld-imm tests" check-jit)))
