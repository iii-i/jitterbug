#lang racket/base

(require
  "../../lib/tests.rkt"
  (only-in "../../s390/spec.rkt" check-jit))

(module+ test
  (time (verify-epilogue "s390-epilogue tests" check-jit)))
