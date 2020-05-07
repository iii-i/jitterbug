#lang racket/base

(require
  "../../lib/tests.rkt"
  (only-in "../../x86_64/spec.rkt" check-jit))

(module+ test
  (time (verify-alu32-x "x86_64-alu32-x tests" check-jit)))