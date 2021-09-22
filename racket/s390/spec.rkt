#lang rosette

(require
  "bpf_jit_comp.rkt"
  "../lib/bpf-common.rkt"
  "../lib/hybrid-memory.rkt"
  "../lib/spec/proof.rkt"
  "../lib/spec/bpf.rkt"
  "../common.rkt"
  (prefix-in core: serval/lib/core)
  (prefix-in bpf: serval/bpf)
  (prefix-in s390: serval/s390))

(provide (all-defined-out))

(define (rounded-stack-depth jit)
  (define aux (bpf_jit-aux jit))
  (define stack_depth (bpf-prog-aux-stack_depth aux))
  (zero-extend (round_up stack_depth (bv 8 32)) (bitvector 64)))

(define (cpu-invariant-registers jit cpu target-pc-base)
  (define memmgr (s390:cpu-memmgr cpu))
  (define litbase (bvadd target-pc-base (zero-extend (bpf_jit-base_ip jit) (type-of target-pc-base))))
  (define stackbase (hybrid-memmgr-stackbase memmgr))
  (define stack_size (rounded-stack-depth jit))
  (list
    (cons 11 litbase)
    (cons 13 stackbase)
    (cons 15 (bvsub stackbase stack_size))))

(define (interpret-program base cpu code run-log)
  (define n (bvsub (s390:cpu-pswa cpu) base))
  (match-define (cons prg_buf prg) code)
  (define prg-bv (zero-extend prg (type-of n)))
  (if (or (term? n) (bvuge n prg-bv))
    ; Control transfer outside of the code range. This might be what we want, just stop.
    run-log
    ; Control transfer inside of the code range. Fetch, decode and interpret the next insn.
    (begin
      (define (fetch i) (core:memmgr-load prg_buf n (bv i (type-of n)) (bv 1 (type-of n))))
      (define insn (s390:decode-one fetch))
      ; JIT generates mostly symbolic opcodes and thus s390:decode-one produces a large union. Since
      ; the generated opcodes are not random, most of this union's branches are infeasible. Pruning them
      ; here decreases the verification time by a factor of ~5.
      (for/all [(insn insn #:exhaustive)]
        (if insn
          (if (sat? (solve #t))
            (begin
              (s390:interpret-insn cpu insn)
              (interpret-program base cpu code (vector-append run-log (vector insn))))
            (core:bug #:msg "Pruned branch reached"))
          (core:bug #:msg "JIT produced an unsupported insn"))))))

(define max-target-size #x80000000)

(define s390-target (make-bpf-target
  #:target-bitwidth 64
  #:big-endian #t
  #:abstract-regs
    (lambda (cpu)
      (apply
        bpf:regs
        (for/list
          [(idx (in-range MAX_BPF_JIT_REG))]
          (define reg (bpf:idx->reg idx))
          (vector-ref
            (s390:cpu-gprs cpu)
            (bitvector->natural (reg2hex reg))))))
  #:emit-insn
    (lambda (i insn next-insn jit)
      (bpf_jit_insn jit i insn next-insn #f (rounded-stack-depth jit))
      (cons (bpf_jit-prg_buf jit) (bpf_jit-prg jit)))
  #:run-code
    (lambda (base cpu code)
      (match-define (cons prg_buf _) code)
      (set-hybrid-memmgr-jitted-code! (s390:cpu-memmgr cpu) prg_buf)
      (interpret-program base cpu code (vector)))
  #:init-cpu
    (lambda (jit target-pc memmgr)
      (define cpu (s390:init-cpu memmgr))
      (s390:set-cpu-pswa! cpu target-pc)
      cpu)
  #:init-arch-invariants!
    (lambda (jit cpu target-pc-base)
      (for ([inv (cpu-invariant-registers jit cpu target-pc-base)])
      (vector-set! (s390:cpu-gprs cpu) (car inv) (cdr inv))))
  #:arch-invariants
    (lambda (jit initial-cpu cpu target-pc-base)
      (and
        (core:bvaligned? (s390:cpu-pswa cpu) (bv 2 64))
        (apply
          &&
          (for/list ([inv (cpu-invariant-registers jit cpu target-pc-base)])
            (equal? (vector-ref (s390:cpu-gprs cpu) (car inv)) (cdr inv))))))
  #:max-target-size max-target-size
  #:init-ctx
    (lambda (insns-addr insn-idx program-length aux)
      (define-symbolic*
        seen
        size
        size_prg
        exit_ip
        r1_thunk_ip
        r14_thunk_ip
        tail_call_start
        excnt
        (bitvector 32))
      (define-symbolic*
        seen_reg
        (bitvector 32))
      (define-symbolic* addrs (~> (bitvector 32) (bitvector 32)))
      (define jit
        (bpf_jit
          seen
          seen_reg
          addrs
          (core:make-flat-memmgr #:big-endian #t) ; prg_buf
          size
          size_prg
          (bv 0 32) ; prg
          (bv #x1000 32) ; lit32_start
          (bv #x1000 32) ; lit32
          (bv #x2000 32) ; lit64_start
          (bv #x2000 32) ; lit64
          (bv 0 32) ; base_ip
          exit_ip
          r1_thunk_ip
          r14_thunk_ip
          tail_call_start
          excnt
          aux))
      jit)
  #:code-size
    (lambda (code)
      (match-define (cons _ prg) code)
      (zero-extend prg (bitvector 64)))
  #:bpf-to-target-pc
    (lambda (jit target-pc-base bpf-pc)
      (define addrs (bpf_jit-addrs jit))
      (define addr (zero-extend (addrs bpf-pc) (bitvector 64)))
      (bvadd target-pc-base addr))
  #:max-stack-usage
    (lambda (jit) (bvadd (bv 160 64) (rounded-stack-depth jit)))
  #:supports-pseudocall #f
  #:simulate-call
    (lambda (cpu call-addr call-fn)
      (define memmgr (s390:cpu-memmgr cpu))

      ; Get arguments and return address.
      (define args
        (for/list
          ([reg (list 2 3 4 5 6)])
          (vector-ref (s390:cpu-gprs cpu) reg)))
      (define retaddr (vector-ref (s390:cpu-gprs cpu) 14))

      ; Model the return value as a fresh arbitrary value.
      (define result
        (core:list->bitvector/le (hybrid-memmgr-get-fresh-bytes memmgr 8)))

      ; Emit an event for the call.
      (hybrid-memmgr-trace-event! memmgr
        (apply call-event call-fn result args))

      ; Havoc caller-saved registers.
      (for ([reg (list 0 1 2 3 4 5 14)])
        (define-symbolic* havoc (bitvector 64))
        (vector-set! (s390:cpu-gprs cpu) reg havoc))
      (define-symbolic* havoc (bitvector 2))
      (s390:set-cpu-cc! cpu havoc)

      ; Set the return value and
      (vector-set! (s390:cpu-gprs cpu) 2 result)
      (s390:set-cpu-pswa! cpu retaddr))
  #:bpf-stack-range
    (lambda (jit)
      (define top (bv 0 64))
      (define bottom (bvsub top (rounded-stack-depth jit)))
      (cons bottom top))
  #:jitted-code-range
    (lambda (jit target-pc-base)
      (cons target-pc-base (bvadd target-pc-base (bv (- max-target-size 1) 64))))
  #:copy-target-cpu
    (lambda (cpu)
      (struct-copy s390:cpu cpu [gprs (vector-copy (s390:cpu-gprs cpu))]))
  #:initial-state?
    (lambda (jit input cpu)
      (define memmgr (s390:cpu-memmgr cpu))
      (define stackbase (hybrid-memmgr-stackbase memmgr))
      (and
        (equal? (vector-ref (s390:cpu-gprs cpu) 15) stackbase)
        (equal? (vector-ref (s390:cpu-gprs cpu) 2) (program-input-r1 input))))
  #:arch-safety
    (lambda (initial final)
      (and
        (equal?
          (s390:cpu-pswa final)
          (vector-ref (s390:cpu-gprs initial) 14))
        (apply
          &&
          (for/list
            ([reg (list 6 7 8 9 10 11 12 13 15)])
            (equal?
              (vector-ref (s390:cpu-gprs final) reg)
              (vector-ref (s390:cpu-gprs initial) reg))))))
  #:epilogue-offset
    (lambda (target-pc-base jit)
      (bvadd
        target-pc-base
        (zero-extend (bpf_jit-exit_ip jit) (bitvector 64))))
  #:ctx-valid?
    (lambda (jit insn-idx)
      (equal?
        (bpf_jit-prg jit)
        ((bpf_jit-addrs jit) insn-idx)))
  #:emit-prologue
    (lambda (jit)
      (bpf_jit_prologue jit (rounded-stack-depth jit))
      (cons (bpf_jit-prg_buf jit) (bpf_jit-prg jit)))
  #:emit-epilogue
    (lambda (jit)
      (bpf_jit_epilogue jit (rounded-stack-depth jit))
      (cons (bpf_jit-prg_buf jit) (bpf_jit-prg jit)))
  #:abstract-return-value
    (lambda (cpu) (core:trunc 32 (vector-ref (s390:cpu-gprs cpu) 2)))
))

(define (check-jit code)
  (verify-bpf-jit/64 code s390-target))
