#lang rosette

; This file is translated and adapted from arch/s390/net/bpf_jit_comp.c,
; which is licensed under:
;
; SPDX-License-Identifier: GPL-2.0

(require
  "../lib/bpf-common.rkt"
  "../lib/bvaxiom.rkt"
  "../common.rkt"
  (prefix-in bpf: serval/bpf)
  serval/lib/bvarith
  (prefix-in core: serval/lib/core)
  serval/lib/debug)

(provide
  (struct-out bpf_jit)
  bpf_jit_insn
  bpf_jit_prologue
  bpf_jit_epilogue
  reg2hex)

; From include/linux/filter.h
(define (insn_is_zext insn)
  (and
    ; ARTIFACT: next-bpf-insn can be #f
    insn
    (equal? (bpf:insn-code insn) '(BPF_ALU BPF_MOV BPF_X))
    (bveq (bpf:insn-imm insn) (bv 1 32))))

; From arch/s390/include/asm/nospec-branch.h
; ARTIFACT: do not verify expolines for now
(define nospec_disable (bv 1 32))

; From bpf_jit.h
(define STK_SPACE_ADD 160)
(define STK_160_UNUSED (- 160 (* 12 8)))
(define STK_OFF (- STK_SPACE_ADD STK_160_UNUSED))
(define STK_OFF_R6 (- 160 (* 11 8)))
(define STK_OFF_TCCNT (- 160 (* 12 8)))

(struct bpf_jit
  (seen                         ; Flags to remember seen eBPF instructions
   seen_reg                     ; REWRITE: Bitmap to remember which registers are used
   addrs                        ; Array with relative instruction addresses
   prg_buf                      ; Start of program
   size                         ; Size of program and literal pool
   size_prg                     ; Size of program
   prg                          ; Current position in program
   lit32_start                  ; Start of 32-bit literal pool
   lit32                        ; Current position in 32-bit literal pool
   lit64_start                  ; Start of 64-bit literal pool
   lit64                        ; Current position in 64-bit literal pool
   base_ip                      ; Base address for literal pool
   exit_ip                      ; Address of exit
   r1_thunk_ip                  ; Address of expoline thunk for 'br %r1'
   r14_thunk_ip                 ; Address of expoline thunk for 'br %r14'
   tail_call_start              ; Tail call start offset
   excnt                        ; Number of exception table entries
   aux)
  #:mutable
  #:transparent)

(define (BIT n) (arithmetic-shift 1 n))
(define SEEN_MEM (BIT 0))               ; use mem[] for temporary storage
(define SEEN_LITERAL (BIT 1))           ; code uses literals
(define SEEN_FUNC (BIT 2))              ; calls C functions
(define SEEN_TAIL_CALL (BIT 3))         ; code uses tail calls
(define SEEN_STACK (bitwise-ior SEEN_FUNC SEEN_MEM))

;
; s390 registers
;
(define REG_W0 (+ MAX_BPF_JIT_REG 0))           ; Work register 1 (even)
(define REG_W1 (+ MAX_BPF_JIT_REG 1))           ; Work register 2 (odd)
(define REG_L (+ MAX_BPF_JIT_REG 2))            ; Literal pool register
(define REG_15 (+ MAX_BPF_JIT_REG 3))           ; Register 15
(define REG_0 REG_W0)                           ; Register 0
(define REG_1 REG_W1)                           ; Register 1
(define REG_2 BPF_REG_1)                        ; Register 2
(define REG_14 BPF_REG_0)                       ; Register 14

;
; Mapping of BPF registers to s390 registers
;
(define (reg2hex reg)
  (cond
    ; Return code
    [(equal? reg BPF_REG_0) (bv 14 32)]
    ; Function parameters
    [(equal? reg BPF_REG_1) (bv 2 32)]
    [(equal? reg BPF_REG_2) (bv 3 32)]
    [(equal? reg BPF_REG_3) (bv 4 32)]
    [(equal? reg BPF_REG_4) (bv 5 32)]
    [(equal? reg BPF_REG_5) (bv 6 32)]
    ; Call saved registers
    [(equal? reg BPF_REG_6) (bv 7 32)]
    [(equal? reg BPF_REG_7) (bv 8 32)]
    [(equal? reg BPF_REG_8) (bv 9 32)]
    [(equal? reg BPF_REG_9) (bv 10 32)]
    ; BPF stack pointer
    [(equal? reg BPF_REG_FP) (bv 13 32)]
    ; Register for blinding
    [(equal? reg BPF_REG_AX) (bv 12 32)]
    ; Work registers for s390x backend
    [(equal? reg REG_W0) (bv 0 32)]
    [(equal? reg REG_W1) (bv 1 32)]
    [(equal? reg REG_L) (bv 11 32)]
    [(equal? reg REG_15) (bv 15 32)]
    ; Unknown register
    [else (bug #:msg (format "Unknown BPF register: ~v" reg))]))

(define (reg dst_reg src_reg)
  (bvor
    (bvshl (reg2hex dst_reg) (bv 4 32))
    (reg2hex src_reg)))

(define (reg_high reg)
  (bvshl (reg2hex reg) (bv 4 32)))

(define (reg_set_seen jit b1)
  (define r1 (reg2hex b1))

  ; REWRITE: use a bitmap
  (when (and (bvuge r1 (bv 6 32)) (bvule r1 (bv 15 32)))
    (set-bpf_jit-seen_reg!
      jit
      (bvor (bpf_jit-seen_reg jit) (bvshl (bv 1 32) r1)))))

(define REG_SET_SEEN reg_set_seen)

; REWRITE: use a bitmap
(define (seen_reg jit i) (not (bvzero? (bvand (bpf_jit-seen_reg jit) (bvshl (bv 1 32) i)))))
(define (REG_SEEN jit b1) (seen_reg jit (reg2hex b1)))

;
; EMIT macros for code generation
;

(define (copy-to-prg-buf! jit offset data)
  (core:memmgr-store!
    (bpf_jit-prg_buf jit)
    (zero-extend offset (bitvector 64))
    (bv 0 64)
    data
    (bv (/ (core:bv-size data) 8) 64)))

(define (_EMIT2 jit op)
  (when (bpf_jit-prg_buf jit)
    (copy-to-prg-buf! jit (bpf_jit-prg jit) (extract 15 0 op)))
  (set-bpf_jit-prg! jit (bvadd (bpf_jit-prg jit) (bv 2 32))))

(define (EMIT2 jit op b1 b2)
  (_EMIT2 jit (bvor op (reg b1 b2)))
  (REG_SET_SEEN jit b1)
  (REG_SET_SEEN jit b2))

(define (_EMIT4 jit op)
  (when (bpf_jit-prg_buf jit)
    (copy-to-prg-buf! jit (bpf_jit-prg jit) op))
  (set-bpf_jit-prg! jit (bvadd (bpf_jit-prg jit) (bv 4 32))))

(define (EMIT4 jit op b1 b2)
  (_EMIT4 jit (bvor op (reg b1 b2)))
  (REG_SET_SEEN jit b1)
  (REG_SET_SEEN jit b2))

(define (EMIT4_RRF jit op b1 b2 b3)
  (_EMIT4 jit (bvor op (bvshl (reg_high b3) (bv 8 32)) (reg b1 b2)))
  (REG_SET_SEEN jit b1)
  (REG_SET_SEEN jit b2)
  (REG_SET_SEEN jit b3))

(define (_EMIT4_DISP jit op disp)
  (define __disp (bvand disp (bv #xfff 32)))
  (_EMIT4 jit (bvor op __disp)))

(define (EMIT4_DISP jit op b1 b2 disp)
  (_EMIT4_DISP jit (bvor op (bvshl (reg_high b1) (bv 16 32)) (bvshl (reg_high b2) (bv 8 32))) disp)
  (REG_SET_SEEN jit b1)
  (REG_SET_SEEN jit b2))

(define (EMIT4_IMM jit op b1 imm)
  (define __imm (bvand imm (bv #xffff 32)))
  (_EMIT4 jit (bvor op (bvshl (reg_high b1) (bv 16 32)) __imm))
  (REG_SET_SEEN jit b1))

(define (EMIT4_PCREL jit op pcrel)
  (define __pcrel (bvand (bvashr pcrel 1) (bv #xffff 32)))
  (_EMIT4 jit (bvor op __pcrel)))

(define (EMIT4_PCREL_RIC jit op mask target)
  (define __rel (bvsdiv (bvsub target (bpf_jit-prg jit)) (bv 2 32)))
  (_EMIT4 jit (bvor op (bvshl mask (bv 20 32)) (bvand __rel (bv #xffff 32)))))

(define (_EMIT6 jit op1 op2)
  (when (bpf_jit-prg_buf jit)
    (copy-to-prg-buf! jit (bpf_jit-prg jit) op1)
    (copy-to-prg-buf! jit (bvadd (bpf_jit-prg jit) (bv 4 32)) (extract 15 0 op2)))
  (set-bpf_jit-prg! jit (bvadd (bpf_jit-prg jit) (bv 6 32))))

(define (_EMIT6_DISP jit op1 op2 disp)
  (define __disp (bvand disp (bv #xfff 32)))
  (_EMIT6 jit (bvor op1 __disp) op2))

(define (_EMIT6_DISP_LH jit op1 op2 disp)
  (define _disp (sign-extend disp (bitvector 32)))
  (define __disp_h (bvand _disp (bv #xff000 32)))
  (define __disp_l (bvand _disp (bv #x00fff 32)))
  (_EMIT6 jit (bvor op1 __disp_l) (bvor op2 (bvashr __disp_h (bv 4 32)))))

(define (EMIT6_DISP_LH jit op1 op2 b1 b2 b3 disp)
  (_EMIT6_DISP_LH
    jit
    (bvor op1 (bvshl (reg b1 b2) (bv 16 32)) (bvshl (reg_high b3) (bv 8 32)))
    op2
    disp)
  (REG_SET_SEEN jit b1)
  (REG_SET_SEEN jit b2)
  (REG_SET_SEEN jit b3))

(define (EMIT6_PCREL_RIEB jit op1 op2 b1 b2 mask target)
  (define rel (bvsdiv (bvsub target (bpf_jit-prg jit)) (bv 2 32)))
  (_EMIT6
    jit
    (bvor op1 (bvshl (reg b1 b2) (bv 16 32)) (bvand rel (bv #xffff 32)))
    (bvor op2 (bvshl mask (bv 12 32)))
    (REG_SET_SEEN jit b1)
    (REG_SET_SEEN jit b2)))

(define (EMIT6_PCREL_RIEC jit op1 op2 b1 imm mask target)
  (define rel (bvsdiv (bvsub target (bpf_jit-prg jit)) (bv 2 32)))
  (_EMIT6
    jit
    (bvor
      op1
      (bvshl (bvor (reg_high b1) mask) (bv 16 32))
      (bvand rel (bv #xffff 32)))
    (bvor op2 (bvshl (bvand imm (bv #xff 32)) (bv 8 32))))
    (REG_SET_SEEN jit b1)
    (bug-assert (bvule imm (bv #xff 32))))

(define (EMIT6_PCREL jit op1 op2 b1 b2 i off mask)
  (define rel
    (bvsdiv
      (bvsub ((bpf_jit-addrs jit) (bvadd i off (bv 1 32))) (bpf_jit-prg jit))
      (bv 2 32)))
  (_EMIT6
    jit
    (bvor op1 (bvshl (reg b1 b2) (bv 16 32)) (bvand rel (bv #xffff 32)))
    (bvor op2 mask))
  (REG_SET_SEEN jit b1)
  (REG_SET_SEEN jit b2))

(define (EMIT6_PCREL_RILB jit op b target)
  (define rel (bvsdiv (bvsub target (bpf_jit-prg jit)) (bv 2 32)))
  (_EMIT6
    jit
    (bvor op (bvshl (reg_high b) (bv 16 32)) (bvlshr rel (bv 16 32)))
    (bvand rel (bv #xffff 32)))
  (REG_SET_SEEN jit b))

(define (EMIT6_PCREL_RIL jit op target)
  (define rel (bvsdiv (bvsub target (bpf_jit-prg jit)) (bv 2 32)))
  (_EMIT6 jit (bvor op (bvlshr rel (bv 16 32))) (bvand rel (bv #xffff 32))))

(define (EMIT6_PCREL_RILC jit op mask target)
  (EMIT6_PCREL_RIL jit (bvor op (bvshl mask (bv 20 32))) (target)))

(define (_EMIT6_IMM jit op imm)
  (define __imm imm)
  (_EMIT6
    jit
    (bvor op (bvlshr __imm (bv 16 32)))
    (bvand __imm (bv #xffff 32))))

(define (EMIT6_IMM jit op b1 imm)
  (_EMIT6_IMM jit (bvor op (bvshl (reg_high b1) (bv 16 32))) imm)
  (REG_SET_SEEN jit b1))

(define (_EMIT_CONST_U32 jit val)
  (define ret (bpf_jit-lit32 jit))
  (when (bpf_jit-prg_buf jit)
    (copy-to-prg-buf! jit (bpf_jit-lit32 jit) val))
  (set-bpf_jit-lit32! jit (bvadd (bpf_jit-lit32 jit) (bv 4 32)))
  ret)

(define (EMIT_CONST_U32 jit val)
  (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_LITERAL 32)))
  (bvsub (_EMIT_CONST_U32 jit val) (bpf_jit-base_ip jit)))

(define (_EMIT_CONST_U64 jit val extend)
  (define ret (bpf_jit-lit64 jit))
  (when (bpf_jit-prg_buf jit)
    (copy-to-prg-buf! jit (bpf_jit-lit64 jit) (extend val (bitvector 64))))
  (set-bpf_jit-lit64! jit (bvadd (bpf_jit-lit64 jit) (bv 8 32)))
  ret)

(define (EMIT_CONST_U64 jit val extend)
  (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_LITERAL 32)))
  (bvsub (_EMIT_CONST_U64 jit val extend) (bpf_jit-base_ip jit)))

(define (EMIT_ZERO jit b1)
  (when (not (bpf-prog-aux-verifier_zext (bpf_jit-aux jit)))
    ; llgfr %dst,%dst (zero extend to 64 bit)
    (EMIT4 jit (bv #xb9160000 32) b1 b1)
    (REG_SET_SEEN jit b1)))

;
; Return whether this is the first pass. The first pass is special, since we
; don't know any sizes yet, and thus must be conservative.
;
(define (is_first_pass jit) (bveq (bpf_jit-size jit) (bv 0 32)))

;
; Return whether this is the code generation pass. The code generation pass is
; special, since we should change as little as possible.
;
(define (is_codegen_pass jit) (bpf_jit-prg_buf jit))

;
; Return whether "rel" can be encoded as a short PC-relative offset
;
(define (is_valid_rel rel)
  (and (bvsge rel (bv -65536 32)) (bvsle rel (bv 65534 32))))

;
; Return whether "off" can be reached using a short PC-relative offset
;
(define (can_use_rel jit off) (is_valid_rel (bvsub off (bpf_jit-prg jit))))

;
; Return whether given displacement can be encoded using
; Long-Displacement Facility
;
(define (is_valid_ldisp disp)
  (and (bvsge disp (bv -524288 32)) (bvsle disp (bv 524287 32))))

;
; Return whether the next 32-bit literal pool entry can be referenced using
; Long-Displacement Facility
;
(define (can_use_ldisp_for_lit32 jit)
  (is_valid_ldisp (bvsub (bpf_jit-lit32 jit) (bpf_jit-base_ip jit))))

;
; Return whether the next 64-bit literal pool entry can be referenced using
; Long-Displacement Facility
;
(define (can_use_ldisp_for_lit64 jit)
  (is_valid_ldisp (bvsub (bpf_jit-lit64 jit) (bpf_jit-base_ip jit))))

;
; Save registers from "rs" (register start) to "re" (register end) on stack
;
(define (save_regs jit rs re)
  (define off (bvadd (bv STK_OFF_R6 32) (bvmul (bvsub rs (bv 6 32)) (bv 8 32))))

  (cond
    [(bveq rs re)
     ; stg %rs,off(%r15)
     (_EMIT6 jit (bvor (bv #xe300f000 32) (bvshl rs (bv 20 32)) off) (bv #x0024 32))]
    [else
     ; stmg %rs,%re,off(%r15)
     (_EMIT6_DISP
       jit
       (bvor (bv #xeb00f000 32) (bvshl rs (bv 20 32)) (bvshl re (bv 16 32))) (bv #x0024 32) off)]))

;
; Restore registers from "rs" (register start) to "re" (register end) on stack
;
(define (restore_regs jit rs re stack_depth)
  (define off (bvadd (bv STK_OFF_R6 32) (bvmul (bvsub rs (bv 6 32)) (bv 8 32))))

  (when (not (bvzero? (bvand (bpf_jit-seen jit) (bv SEEN_STACK 32))))
    (set! off (bvadd (off (bv STK_OFF 32) stack_depth))))

  (cond
    [(bveq rs re)
     ; lg %rs,off(%r15)
     (_EMIT6 jit (bvor (bv #xe300f000 32) (bvshl rs (bv 20 32)) off) (bv #x0004 32))]
    [else
     ; lmg %rs,%re,off(%r15)
     (_EMIT6_DISP
       jit
       (bvor (bv #xeb00f000 32) (bvshl rs (bv 20 32)) (bvshl re (bv 16 32))) (bv #x0004 32) off)]))

;
; Return first seen register (from start)
;
(define (get_start jit start)
  ; REWRITE: use recursion
  (define i start)
  (cond
    [(bvsle i (bv 15 32)) (if (seen_reg jit i) i (get_start jit (bvadd1 start)))]
    [else (bv 0 32)]))

;
; Return last seen register (from start) (gap >= 2)
;
(define (get_end jit start)
  ; REWRITE: use recursion
  (define i start)
  (cond
    [(bvslt i (bv 15 32))
     (if (and (not (seen_reg jit i)) (not (seen_reg jit (bvadd1 i)))) (bvsub1 i) (get_end jit (bvadd1 i)))]
    [else
     (if (seen_reg jit (bv 15 32)) (bv 15 32) (bv 14 32))]))

(define REGS_SAVE 1)
(define REGS_RESTORE 0)
;
; Save and restore clobbered registers (6-15) on stack.
; We save/restore registers in chunks with gap >= 2 registers.
;
(define (save_restore_regs jit op stack_depth)
  (define last (bv 15 32))
  (define save_restore_size (bv 6 32))
  (define re (bv 6 32))

  (cond
    [(is_first_pass jit)
     ;
     ; We don't know yet which registers are used. Reserve space
     ; conservatively.
     ;
     (set-bpf_jit-prg!
       jit
       (bvadd (bpf_jit-prg jit) (bvmul (bvadd (bvsub last re) (bv 1 32)) save_restore_size)))]
    [else
     (define (loop)
       (define rs (get_start jit re))
       (when (not (bvzero? rs))
         (define re (get_end jit (bvadd1 rs)))
         (cond
           [(bveq op (bv REGS_SAVE 32))
            (save_regs jit rs re)]
           [else
            (restore_regs jit rs re stack_depth)])
         (set! re (bvadd1 re))
         (when (bvsle re last) (loop))))
     (loop)]))

;
; Emit function prologue
;
; Save registers and create stack frame if necessary.
; See stack frame layout desription in "bpf_jit.h"!
;
(define (bpf_jit_prologue jit stack_depth)
  #f)

;
; Function epilogue
;
(define (bpf_jit_epilogue jit stack_depth)
  #f)

;
; Compile one eBPF instruction into s390x code
;
(define (bpf_jit_insn jit i insn next-insn extra_pass stack_depth)
  (define dst_reg (bpf:insn-dst insn))
  (define src_reg (bpf:insn-src insn))
  (define insn_count 1)
  (define imm (bpf:insn-imm insn))
  (define off (bpf:insn-off insn))

  (case (bpf:insn-code insn)
    ;
    ; BPF_MOV
    ;
    [((BPF_ALU BPF_MOV BPF_X)) ; dst = (u32) src
     ; llgfr %dst,%src
     (EMIT4 jit (bv #xb9160000 32) dst_reg src_reg)
     (when (insn_is_zext next-insn) (set! insn_count 2))]
    [((BPF_ALU64 BPF_MOV BPF_X)) ; dst = src
     ; lgr %dst,%src
     (EMIT4 jit (bv #xb9040000 32) dst_reg src_reg)]
    [((BPF_ALU BPF_MOV BPF_K)) ; dst = (u32) imm
     ; llilf %dst,imm
     (EMIT6_IMM jit (bv #xc00f0000 32) dst_reg imm)
     (when (insn_is_zext next-insn) (set! insn_count 2))]
    [((BPF_ALU64 BPF_MOV BPF_K)) ; dst = imm
     ; lgfi %dst,imm
     (EMIT6_IMM jit (bv #xc0010000 32) dst_reg imm)]
    ;
    ; BPF_LD 64
    ;
    [((BPF_LD BPF_IMM BPF_DW)) ; dst = (u64) imm
     ; 16 byte instruction that uses two 'struct bpf_insn'
     (define imm64
       (bvor
         (zero-extend imm (bitvector 64))
         (bvshl
           (zero-extend (bpf:insn-imm next-insn) (bitvector 64))
           (bv 32 64))))
     ; lgrl %dst,imm
     (EMIT6_PCREL_RILB jit (bv #xc4080000 32) dst_reg (_EMIT_CONST_U64 jit imm64 zero-extend))
     (set! insn_count 2)]
     ;
     ; BPF_ADD
     ;
     [((BPF_ALU BPF_ADD BPF_X)) ; dst = (u32) dst + (u32) src
      ; ar %dst,%src
      (EMIT2 jit (bv #x1a00 32) dst_reg src_reg)
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_ADD BPF_X)) ; dst = dst + src
      ; agr %dst,%src
      (EMIT4 jit (bv #xb9080000 32) dst_reg src_reg)]
     [((BPF_ALU BPF_ADD BPF_K)) ; dst = (u32) dst + (u32) imm
      (when (not (bveq imm (bv 0 32)))
        ; alfi %dst,imm
        (EMIT6_IMM jit (bv #xc20b0000 32) dst_reg imm))
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_ADD BPF_K)) ; dst = dst + imm
      (when (not (bveq imm (bv 0 32)))
        ; agfi %dst,imm
        (EMIT6_IMM jit (bv #xc2080000 32) dst_reg imm))]
     ;
     ; BPF_SUB
     ;
     [((BPF_ALU BPF_SUB BPF_X)) ; dst = (u32) dst - (u32) src
      ; sr %dst,%src
      (EMIT2 jit (bv #x1b00 32) dst_reg src_reg)
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_SUB BPF_X)) ; dst = dst - src
      ; sgr %dst,%src
      (EMIT4 jit (bv #xb9090000 32) dst_reg src_reg)]
     [((BPF_ALU BPF_SUB BPF_K)) ; dst = (u32) dst - (u32) imm
      (when (not (bveq imm (bv 0 32)))
        ; alfi %dst,-imm
        (EMIT6_IMM jit (bv #xc20b0000 32) dst_reg (bvneg imm)))
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_SUB BPF_K)) ; dst = dst - imm
      (when (not (bveq imm (bv 0 32)))
        (cond
          [(bveq imm (bvneg (bv #x80000000 32)))
           ; algfi %dst,0x80000000
           (EMIT6_IMM jit (bv #xc20a0000 32) dst_reg (bv #x80000000 32))]
          [else
           ; agfi %dst,-imm
           (EMIT6_IMM jit (bv #xc2080000 32) dst_reg (bvneg imm))]))]
     ;
     ; BPF_MUL
     ;
     [((BPF_ALU BPF_MUL BPF_X)) ; dst = (u32) dst * (u32) src
      ; msr %dst,%src
      (EMIT4 jit (bv #xb2520000 32) dst_reg src_reg)
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_MUL BPF_X)) ; dst = dst * src
      ; msgr %dst,%src
      (EMIT4 jit (bv #xb90c0000 32) dst_reg src_reg)]
     [((BPF_ALU BPF_MUL BPF_K)) ; dst = (u32) dst * (u32) imm
      (when (not (bveq imm (bv 1 32)))
        ; msfi %r5,imm
        (EMIT6_IMM jit (bv #xc2010000 32) dst_reg imm))
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_MUL BPF_K)) ; dst = dst * imm
      (when (not (bveq imm (bv 1 32)))
        ; msgfi %dst,imm
        (EMIT6_IMM jit (bv #xc2000000 32) dst_reg imm))]
     ;
     ; BPF_DIV / BPF_MOD
     ;
     [((BPF_ALU BPF_DIV BPF_X) ; dst = (u32) dst / (u32) src
       (BPF_ALU BPF_MOD BPF_X)) ; dst = (u32) dst % (u32) src
      (define rc_reg
        (if (equal? (BPF_OP (bpf:insn-code insn)) 'BPF_DIV) REG_W1 REG_W0))
      ; lhi %w0,0
      (EMIT4_IMM jit (bv #xa7080000 32) REG_W0 (bv 0 32))
      ; lr %w1,%dst
      (EMIT2 jit (bv #x1800 32) REG_W1 dst_reg)
      ; dlr %w0,%src
      (EMIT4 jit (bv #xb9970000 32) REG_W0 src_reg)
      ; llgfr %dst,%rc
      (EMIT4 jit (bv #xb9160000 32) dst_reg rc_reg)
      (when (insn_is_zext next-insn) (set! insn_count 2))]
     [((BPF_ALU64 BPF_DIV BPF_X) ; dst = dst / src
       (BPF_ALU64 BPF_MOD BPF_X)) ; dst = dst % src
      (define rc_reg
        (if (equal? (BPF_OP (bpf:insn-code insn)) 'BPF_DIV) REG_W1 REG_W0))
      ; lghi %w0,0
      (EMIT4_IMM jit (bv #xa7090000 32) REG_W0 (bv 0 32))
      ; lgr %w1,%dst
      (EMIT4 jit (bv #xb9040000 32) REG_W1 dst_reg)
      ; dlgr %w0,%dst
      (EMIT4 jit (bv #xb9870000 32) REG_W0 src_reg)
      ; lgr %dst,%rc
      (EMIT4 jit (bv #xb9040000 32) dst_reg rc_reg)]
     [((BPF_ALU BPF_DIV BPF_K) ; dst = (u32) dst / (u32) imm
       (BPF_ALU BPF_MOD BPF_K)) ; dst = (u32) dst % (u32) imm
      (define rc_reg
        (if (equal? (BPF_OP (bpf:insn-code insn)) 'BPF_DIV) REG_W1 REG_W0))
      (cond
        [(bveq imm (bv 1 32))
         (cond
           [(equal? (BPF_OP (bpf:insn-code insn)) 'BPF_MOD)
            ; lhgi %dst,0
            (EMIT4_IMM jit (bv #xa7090000 32) dst_reg (bv 0 32))]
           [else
            (EMIT_ZERO jit dst_reg)])]
        [else
         ; lhi %w0,0
         (EMIT4_IMM jit (bv #xa7080000 32) REG_W0 (bv 0 32))
         ; lr %w1,%dst
         (EMIT2 jit (bv #x1800 32) REG_W1 dst_reg)
         (cond
           [(and (not (is_first_pass jit)) (can_use_ldisp_for_lit32 jit))
            ; dl %w0,<d(imm)>(%l)
            (EMIT6_DISP_LH
              jit
              (bv #xe3000000 32)
              (bv #x0097 32)
              REG_W0
              REG_0
              REG_L
              (EMIT_CONST_U32 jit imm))]
           [else
            ; lgfrl %dst,imm
            (EMIT6_PCREL_RILB jit (bv #xc40c0000 32) dst_reg (_EMIT_CONST_U32 jit imm))
            (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_LITERAL 32)))
            ; dlr %w0,%dst
            (EMIT4 jit (bv #xb9970000 32) REG_W0 dst_reg)])
         ; llgfr %dst,%rc
         (EMIT4 jit (bv #xb9160000 32) dst_reg rc_reg)
         (when (insn_is_zext next-insn) (set! insn_count 2))])]
     [((BPF_ALU64 BPF_DIV BPF_K) ; dst = dst / imm
       (BPF_ALU64 BPF_MOD BPF_K)) ; dst = dst % imm
      (define rc_reg
        (if (equal? (BPF_OP (bpf:insn-code insn)) 'BPF_DIV) REG_W1 REG_W0))
      (cond
        [(bveq imm (bv 1 32))
         (when (equal? (BPF_OP (bpf:insn-code insn)) 'BPF_MOD)
           ; lhgi %dst,0
           (EMIT4_IMM jit (bv #xa7090000 32) dst_reg (bv 0 32)))]
        [else
         ; lghi %w0,0
         (EMIT4_IMM jit (bv #xa7090000 32) REG_W0 (bv 0 32))
         ; lgr %w1,%dst
         (EMIT4 jit (bv #xb9040000 32) REG_W1 dst_reg)
         (cond
           [(and (not (is_first_pass jit)) (can_use_ldisp_for_lit64 jit))
            ; dlg %w0,<d(imm)>(%l)
            (EMIT6_DISP_LH
              jit
              (bv #xe3000000 32)
              (bv #x0087 32)
              REG_W0
              REG_0
              REG_L
              (EMIT_CONST_U64 jit imm sign-extend))]
           [else
            ; lgrl %dst,imm
            (EMIT6_PCREL_RILB jit (bv #xc4080000 32) dst_reg (_EMIT_CONST_U64 jit imm sign-extend))
            (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_LITERAL 32)))
            ; dlgr %w0,%dst
            (EMIT4 jit (bv #xb9870000 32) REG_W0 dst_reg)])
         ; lgr %dst,%rc
         (EMIT4 jit (bv #xb9040000 32) dst_reg rc_reg)])]
     ;
     ; BPF_AND
     ;
     [((BPF_ALU BPF_AND BPF_X)) ; dst = (u32) dst & (u32) src
      ; nr %dst,%src
      (EMIT2 jit (bv #x1400 32) dst_reg src_reg)
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_AND BPF_X)) ; dst = dst & src
      ; ngr %dst,%src
      (EMIT4 jit (bv #xb9800000 32) dst_reg src_reg)]
     [((BPF_ALU BPF_AND BPF_K)) ; dst = (u32) dst & (u32) imm
      ; nilf %dst,imm
      (EMIT6_IMM jit (bv #xc00b0000 32) dst_reg imm)
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_AND BPF_K)) ; dst = dst & imm
      (cond
        [(and (not (is_first_pass jit)) (can_use_ldisp_for_lit64 jit))
         ; ng %dst,<d(imm)>(%l)
         (EMIT6_DISP_LH
           jit
           (bv #xe3000000 32)
           (bv #x0080 32)
           dst_reg
           REG_0
           REG_L
           (EMIT_CONST_U64 jit imm sign-extend))]
        [else
         ; lgrl %w0,imm
         (EMIT6_PCREL_RILB jit (bv #xc4080000 32) REG_W0 (_EMIT_CONST_U64 jit imm sign-extend))
         (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_LITERAL 32)))
         ; ngr %dst,%w0
         (EMIT4 jit (bv #xb9800000 32) dst_reg REG_W0)])]
     ;
     ; BPF_OR
     ;
     [((BPF_ALU BPF_OR BPF_X)) ; dst = (u32) dst | (u32) src
      ; or %dst,%src
      (EMIT2 jit (bv #x1600 32) dst_reg src_reg)
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_OR BPF_X)) ; dst = dst | src
      ; ogr %dst,%src
      (EMIT4 jit (bv #xb9810000 32) dst_reg src_reg)]
     [((BPF_ALU BPF_OR BPF_K)) ; dst = (u32) dst | (u32) imm
      ; oilf %dst,imm
      (EMIT6_IMM jit (bv #xc00d0000 32) dst_reg imm)
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_OR BPF_K)) ; dst = dst | imm
      (cond
        [(and (not (is_first_pass jit)) (can_use_ldisp_for_lit64 jit))
         ; og %dst,<d(imm)>(%l)
         (EMIT6_DISP_LH
           jit
           (bv #xe3000000 32)
           (bv #x0081 32)
           dst_reg
           REG_0
           REG_L
           (EMIT_CONST_U64 jit imm sign-extend))]
        [else
         ; lgrl %w0,imm
         (EMIT6_PCREL_RILB jit (bv #xc4080000 32) REG_W0 (_EMIT_CONST_U64 jit imm sign-extend))
         (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_LITERAL 32)))
         ; ogr %dst,%w0
         (EMIT4 jit (bv #xb9810000 32) dst_reg REG_W0)])]
     ;
     ; BPF_XOR
     ;
     [((BPF_ALU BPF_XOR BPF_X)) ; dst = (u32) dst ^ (u32) src
      ; xr %dst,%src
      (EMIT2 jit (bv #x1700 32) dst_reg src_reg)
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_XOR BPF_X)) ; dst = dst ^ src
      ; xgr %dst,%src
      (EMIT4 jit (bv #xb9820000 32) dst_reg src_reg)]
     [((BPF_ALU BPF_XOR BPF_K)) ; dst = (u32) dst ^ (u32) imm
      (when (not (bveq imm (bv 0 32)))
        ; xilf %dst,imm
        (EMIT6_IMM jit (bv #xc0070000 32) dst_reg imm))
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_XOR BPF_K)) ; dst = dst ^ imm
      (cond
        [(and (not (is_first_pass jit)) (can_use_ldisp_for_lit64 jit))
         ; xg %dst,<d(imm)>(%l)
         (EMIT6_DISP_LH
           jit
           (bv #xe3000000 32)
           (bv #x0082 32)
           dst_reg
           REG_0
           REG_L
           (EMIT_CONST_U64 jit imm sign-extend))]
        [else
         ; lgrl %w0,imm
         (EMIT6_PCREL_RILB jit (bv #xc4080000 32) REG_W0 (_EMIT_CONST_U64 jit imm sign-extend))
         (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_LITERAL 32)))
         ; xgr %dst,%w0
         (EMIT4 jit (bv #xb9820000 32) dst_reg REG_W0)])]
     ;
     ; BPF_LSH
     ;
     [((BPF_ALU BPF_LSH BPF_X)) ; dst = (u32) dst << (u32) src
      ; sll %dst,0(%src)
      (EMIT4_DISP jit (bv #x89000000 32) dst_reg src_reg (bv 0 32))
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_LSH BPF_X)) ; dst = dst << src
      ; sllg %dst,%dst,0(%src)
      (EMIT6_DISP_LH jit (bv #xeb000000 32) (bv #x000d 32) dst_reg dst_reg src_reg (bv 0 32))]
     [((BPF_ALU BPF_LSH BPF_K)) ; dst = (u32) dst << (u32) imm
      (when (not (bveq imm (bv 0 32)))
        ; sll %dst,imm(%r0)
        (EMIT4_DISP jit (bv #x89000000 32) dst_reg REG_0 imm))
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_LSH BPF_K)) ; dst = dst << imm
      (when (not (bveq imm (bv 0 32)))
        ; sllg %dst,%dst,imm(%r0)
        (EMIT6_DISP_LH jit (bv #xeb000000 32) (bv #x000d 32) dst_reg dst_reg REG_0 imm))]
     ;
     ; BPF_RSH
     ;
     [((BPF_ALU BPF_RSH BPF_X)) ; dst = (u32) dst >> (u32) src
      ; srl %dst,0(%src)
      (EMIT4_DISP jit (bv #x88000000 32) dst_reg src_reg (bv 0 32))
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_RSH BPF_X)) ; dst = dst >> src
      ; srlg %dst,%dst,0(%src)
      (EMIT6_DISP_LH jit (bv #xeb000000 32) (bv #x000c 32) dst_reg dst_reg src_reg (bv 0 32))]
     [((BPF_ALU BPF_RSH BPF_K)) ; dst = (u32) dst >> (u32) imm
      (when (not (bveq imm (bv 0 32)))
        ; srl %dst,imm(%r0)
        (EMIT4_DISP jit (bv #x88000000 32) dst_reg REG_0 imm))
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_RSH BPF_K)) ; dst = dst >> imm
      (when (not (bveq imm (bv 0 32)))
        ; srlg %dst,%dst,imm(%r0)
        (EMIT6_DISP_LH jit (bv #xeb000000 32) (bv #x000c 32) dst_reg dst_reg REG_0 imm))]
     ;
     ; BPF_ARSH
     ;
     [((BPF_ALU BPF_ARSH BPF_X)) ; ((s32) dst) >>= src
      ; sra %dst,%dst,0(%src)
      (EMIT4_DISP jit (bv #x8a000000 32) dst_reg src_reg (bv 0 32))
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_ARSH BPF_X)) ; ((s64) dst) >>= src
      ; srag %dst,%dst,0(%src)
      (EMIT6_DISP_LH jit (bv #xeb000000 32) (bv #x000a 32) dst_reg dst_reg src_reg (bv 0 32))]
     [((BPF_ALU BPF_ARSH BPF_K)) ; ((s32) dst >> imm
      (when (not (bveq imm (bv 0 32)))
        ; sra %dst,imm(%r0)
        (EMIT4_DISP jit (bv #x8a000000 32) dst_reg REG_0 imm))
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_ARSH BPF_K)) ; ((s64) dst) >>= imm
      (when (not (bveq imm (bv 0 32)))
        ; srag %dst,%dst,imm(%r0)
        (EMIT6_DISP_LH jit (bv #xeb000000 32) (bv #x000a 32) dst_reg dst_reg REG_0 imm))]
     ;
     ; BPF_NEG
     ;
     [((BPF_ALU BPF_NEG)) ; dst = (u32) -dst
      ; lcr %dst,%dst
      (EMIT2 jit (bv #x1300 32) dst_reg dst_reg)
      (EMIT_ZERO jit dst_reg)]
     [((BPF_ALU64 BPF_NEG)) ; dst = -dst
      ; lcgr %dst,%dst
      (EMIT4 jit (bv #xb9030000 32) dst_reg dst_reg)]
     ;
     ; BPF_FROM_BE/LE
     ;
     [((BPF_ALU BPF_END BPF_FROM_BE))
      ; s390 is big endian, therefore only clear high order bytes
      (cond
        [(bveq imm (bv 16 32)) ; dst = (u16) cpu_to_be16(dst)
         ; llghr %dst,%dst
         (EMIT4 jit (bv #xb9850000 32) dst_reg dst_reg)
         (when (insn_is_zext next-insn) (set! insn_count 2))]
        [(bveq imm (bv 32 32)) ; dst = (u32) cpu_to_be32(dst)
         (when (not (bpf-prog-aux-verifier_zext (bpf_jit-aux jit)))
           ; llgfr %dst,%dst
           (EMIT4 jit (bv #xb9160000 32) dst_reg dst_reg))]
        [(bveq imm (bv 64 32)) ; dst = (u64) cpu_to_be64(dst)
         #f])]
     [((BPF_ALU BPF_END BPF_FROM_LE))
      (cond
        [(bveq imm (bv 16 32)) ; dst = (u16) cpu_to_le16(dst)
         ; lrvr %dst,%dst
         (EMIT4 jit (bv #xb91f0000 32) dst_reg dst_reg)
         ; srl %dst,16(%r0)
         (EMIT4_DISP jit (bv #x88000000 32) dst_reg REG_0 (bv 16 32))
         ; llghr %dst,%dst
         (EMIT4 jit (bv #xb9850000 32) dst_reg dst_reg)
         (when (insn_is_zext next-insn) (set! insn_count 2))]
        [(bveq imm (bv 32 32)) ; dst = (u32) cpu_to_le32(dst)
         ; lrvr %dst,%dst
         (EMIT4 jit (bv #xb91f0000 32) dst_reg dst_reg)
         (when (not (bpf-prog-aux-verifier_zext (bpf_jit-aux jit)))
           ; llgfr %dst,%dst
           (EMIT4 jit (bv #xb9160000 32) dst_reg dst_reg))]
        [(bveq imm (bv 64 32)) ; dst = (u64) cpu_to_le64(dst)
         ; lrvgr %dst,%dst
         (EMIT4 jit (bv #xb90f0000 32) dst_reg dst_reg)])]
     ;
     ; BPF_NOSPEC (speculation barrier)
     ;
     [((BPF_ST BPF_NOSPEC))
      #f]
     ;
     ; BPF_ST(X)
     ;
     [((BPF_STX BPF_MEM BPF_B)) ; *(u8 *)(dst + off) = src_reg
      ; stcy %src,off(%dst)
      (EMIT6_DISP_LH
        jit
        (bv #xe3000000 32)
        (bv #x0072 32)
        src_reg
        dst_reg
        REG_0
        (sign-extend off (bitvector 32)))
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))]
     [((BPF_STX BPF_MEM BPF_H)) ; (u16 *)(dst + off) = src
      ; sthy %src,off(%dst)
      (EMIT6_DISP_LH
        jit
        (bv #xe3000000 32)
        (bv #x0070 32)
        src_reg
        dst_reg
        REG_0
        (sign-extend off (bitvector 32)))
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))]
     [((BPF_STX BPF_MEM BPF_W)) ; *(u32 *)(dst + off) = src
      ; sty %src,off(%dst)
      (EMIT6_DISP_LH
        jit
        (bv #xe3000000 32)
        (bv #x0050 32)
        src_reg
        dst_reg
        REG_0
        (sign-extend off (bitvector 32)))
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))]
     [((BPF_STX BPF_MEM BPF_DW)) ; (u64 *)(dst + off) = src
      ; stg %src,off(%dst)
      (EMIT6_DISP_LH
        jit
        (bv #xe3000000 32)
        (bv #x0024 32)
        src_reg
        dst_reg
        REG_0
        (sign-extend off (bitvector 32)))
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))]
     [((BPF_ST BPF_MEM BPF_B)) ; *(u8 *)(dst + off) = imm
      ; lhi %w0,imm
      (EMIT4_IMM jit (bv #xa7080000 32) REG_W0 (bvand imm (bv #xff 32)))
      ; stcy %w0,off(dst)
      (EMIT6_DISP_LH
        jit
        (bv #xe3000000 32)
        (bv #x0072 32)
        REG_W0
        dst_reg
        REG_0
        (sign-extend off (bitvector 32)))
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))]
     [((BPF_ST BPF_MEM BPF_H)) ; (u16 *)(dst + off) = imm
      ; lhi %w0,imm
      (EMIT4_IMM jit (bv #xa7080000 32) REG_W0 (bvand imm (bv #xffff 32)))
      ; sthy %w0,off(dst)
      (EMIT6_DISP_LH
        jit
        (bv #xe3000000 32)
        (bv #x0070 32)
        REG_W0
        dst_reg
        REG_0
        (sign-extend off (bitvector 32)))
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))]
     [((BPF_ST BPF_MEM BPF_W)) ; *(u32 *)(dst + off) = imm
      ; llilf %w0,imm
      (EMIT6_IMM jit (bv #xc00f0000 32) REG_W0 (bvand imm (bv #xffffffff 32)))
      ; sty %w0,off(%dst)
      (EMIT6_DISP_LH
        jit
        (bv #xe3000000 32)
        (bv #x0050 32)
        REG_W0
        dst_reg
        REG_0
        (sign-extend off (bitvector 32)))
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))]
     [((BPF_ST BPF_MEM BPF_DW)) ; *(u64 *)(dst + off) = imm
      ; lgfi %w0,imm
      (EMIT6_IMM jit (bv #xc0010000 32) REG_W0 imm)
      ; stg %w0,off(%dst)
      (EMIT6_DISP_LH
        jit
        (bv #xe3000000 32)
        (bv #x0024 32)
        REG_W0
        dst_reg
        REG_0
        (sign-extend off (bitvector 32)))
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))]
     ;
     ; BPF_ATOMIC
     ;
     [((BPF_STX BPF_ATOMIC BPF_DW)
       (BPF_STX BPF_ATOMIC BPF_W))
      (define is32 (equal? (BPF_SIZE (bpf:insn-code insn)) 'BPF_W))
      (define (EMIT_ATOMIC op32 op64)
        (EMIT6_DISP_LH
          jit
          (bv #xeb000000 32)
          (if is32 op32 op64)
          (if (member 'BPF_FETCH (bpf:insn-imm insn)) src_reg REG_W0)
          src_reg
          dst_reg
          off)
        (when (and is32 (member 'BPF_FETCH (bpf:insn-imm insn))) (EMIT_ZERO jit src_reg)))
      (case (bpf:insn-imm insn)
        ; {op32|op64} {%w0|%src},%src,off(%dst)
        [((BPF_ADD)
          (BPF_ADD BPF_FETCH))
         ; {laal|laalg}
         (EMIT_ATOMIC (bv #x00fa 32) (bv #x00ea 32))]
        [((BPF_AND)
          (BPF_AND BPF_FETCH))
         ; {lan|lang}
         (EMIT_ATOMIC (bv #x00f4 32) (bv #x00e4 32))]
        [((BPF_OR)
          (BPF_OR BPF_FETCH))
         ; {lao|laog}
         (EMIT_ATOMIC (bv #x00f6 32) (bv #x00e6 32))]
        [((BPF_XOR)
          (BPF_XOR BPF_FETCH))
         ; {lax|laxg}
         (EMIT_ATOMIC (bv #x00f7 32) (bv #x00e7 32))]
        [((BPF_XCHG))
         ; {ly|lg} %w0,off(%dst)
         (EMIT6_DISP_LH
           jit
           (bv #xe3000000 32)
           (if is32 (bv #x0058 32) (bv #x0004 32))
           REG_W0
           REG_0
           dst_reg
           off)
         ; 0: {csy|csg} %w0,%src,off(%dst)
         (EMIT6_DISP_LH
           jit
           (bv #xeb000000 32)
           (if is32 (bv #x0014 32) (bv #x0030 32))
           REG_W0
           src_reg
           dst_reg
           off)
         ; brc 4,0b
         (EMIT4_PCREL_RIC jit (bv #xa7040000 32) (bv 4 32) (bvsub (bpf_jit-prg jit) (bv 6 32)))
         ; {llgfr|lgr} %src,%w0
         (EMIT4 jit (if is32 (bv #xb9160000 32) (bv #xb9040000 32)) src_reg REG_W0)
         (when (insn_is_zext next-insn) (set! insn_count 2))]
        [((BPF_CMPXCHG))
         ; 0: {csy|csg} %b0,%src,off(%dst)
         (EMIT6_DISP_LH
           jit
           (bv #xeb000000 32)
           (if is32 (bv #x0014 32) (bv #x0030 32))
           BPF_REG_0
           src_reg
           dst_reg
           off)]
        [else
         (bug #:msg (format "Unknown atomic operation ~v\n" (bpf:insn-imm insn)))])
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))]
     ;
     ; BPF_LDX
     ;
     [((BPF_LDX BPF_MEM BPF_B) ; dst = *(u8 *)(ul) (src + off)
       (BPF_LDX BPF_PROBE_MEM BPF_B))
      ; llgc %dst,0(off,%src)
      (EMIT6_DISP_LH jit (bv #xe3000000 32) (bv #x0090 32) dst_reg src_reg REG_0 off)
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))
      (when (insn_is_zext next-insn) (set! insn_count 2))]
     [((BPF_LDX BPF_MEM BPF_H) ; dst = *(u16 *)(ul) (src + off)
       (BPF_LDX BPF_PROBE_MEM BPF_H))
      ; llgh %dst,0(off,%src)
      (EMIT6_DISP_LH jit (bv #xe3000000 32) (bv #x0091 32) dst_reg src_reg REG_0 off)
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))
      (when (insn_is_zext next-insn) (set! insn_count 2))]
     [((BPF_LDX BPF_MEM BPF_W) ; dst = *(u32 *)(ul) (src + off)
       (BPF_LDX BPF_PROBE_MEM BPF_W))
      ; llgf %dst,off(%src)
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))
      (EMIT6_DISP_LH jit (bv #xe3000000 32) (bv #x0016 32) dst_reg src_reg REG_0 off)
      (when (insn_is_zext next-insn) (set! insn_count 2))]
     [((BPF_LDX BPF_MEM BPF_DW) ; dst = *(u64 *)(ul) (src + off)
       (BPF_LDX BPF_PROBE_MEM BPF_DW))
      ; lg %dst,0(off,%src)
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_MEM 32)))
      (EMIT6_DISP_LH jit (bv #xe3000000 32) (bv #x0004 32) dst_reg src_reg REG_0 off)]
     ;
     ; BPF_JMP / CALL
     ;
     [((BPF_JMP BPF_CALL))
      (define &func (box (void)))
      (define &func_addr_fixed (box (void)))
      (define ret (bpf_jit_get_func_addr jit insn &func &func_addr_fixed))
      (set! ret (bv 0 32)) ; ARTIFACT: bpf_jit_get_func_addr() returns int.
      (cond
        [(bvslt ret (bv 0 32)) -1]
        [else
         (REG_SET_SEEN jit BPF_REG_5)
         (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_FUNC 32)))
         ; lgrl %w1,func
         (EMIT6_PCREL_RILB jit (bv #xc4080000 32) REG_W1 (_EMIT_CONST_U64 jit (unbox &func) zero-extend))
         (cond
           [(bvzero? nospec_disable)
            ; brasl %r14,__s390_indirect_jump_r1
            (EMIT6_PCREL_RILB jit (bv #xc0050000 32) REG_14 (bpf_jit-r1_thunk_ip jit))]
           [else
            ; basr %r14,%w1
            (EMIT2 jit (bv #x0d00 32) REG_14 REG_W1)])
         ; lgr %b0,%r2: load return value into %b0
         (EMIT4 jit (bv #xb9040000 32) BPF_REG_0 REG_2)])]
     [((BPF_JMP BPF_TAIL_CALL))
      ;
      ; Implicit input:
      ;  B1: pointer to ctx
      ;  B2: pointer to bpf_array
      ;  B3: index in bpf_array
      ;
      (set-bpf_jit-seen! jit (bvor (bpf_jit-seen jit) (bv SEEN_TAIL_CALL 32)))

      ;
      ; if (index >= array->map.max_entries)
      ;         goto out;
      ;

      ; llgf %w1,map.max_entries(%b2)
      ; ARTIFACT: offsetof(struct bpf_array, map.max_entries) == 0
      (EMIT6_DISP_LH
        jit
        (bv #xe3000000 32)
        (bv #x0016 32)
        REG_W1
        REG_0
        BPF_REG_2
        (bv 0 32))
      ; if ((u32)%b3 >= (u32)%w1) goto out;
      ; clrj %b3,%w1,0xa,out
      (define patch_1_clrj (bpf_jit-prg jit))
      (EMIT6_PCREL_RIEB
        jit
        (bv #xec000000 32)
        (bv #x0077 32)
        BPF_REG_3
        REG_W1
        (bv #xa 32)
        (bpf_jit-prg jit))

      ;
      ; if (tail_call_cnt++ > MAX_TAIL_CALL_CNT)
      ;         goto out;
      ;

      (cond
        [(not (bvzero? (bvand (bpf_jit-seen jit) (bv SEEN_STACK 32))))
         (set! off (extract 15 0 (bvadd (bv STK_OFF_TCCNT 32) (bv STK_OFF 32) stack_depth)))]
        [else
         (set! off (bv STK_OFF_TCCNT 16))])
      ; lhi %w0,1
      (EMIT4_IMM jit (bv #xa7080000 32) REG_W0 (bv 1 32))
      ; laal %w1,%w0,off(%r15)
      (EMIT6_DISP_LH jit (bv #xeb000000 32) (bv #x00fa 32) REG_W1 REG_W0 REG_15 off)
      ; clij %w1,MAX_TAIL_CALL_CNT,0x2,out
      (define patch_2_clij (bpf_jit-prg jit))
      (EMIT6_PCREL_RIEC jit (bv #xec000000 32) (bv #x007f 32) REG_W1 MAX_TAIL_CALL_CNT 2 (bpf_jit-prg jit))

      ;
      ; prog = array->ptrs[index];
      ; if (prog == NULL)
      ;         goto out;
      ;

      ; llgfr %r1,%b3: %r1 = (u32) index
      (EMIT4 jit (bv #xb9160000 REG_1 BPF_REG_3))
      ; sllg %r1,%r1,3: %r1 *= 8
      (EMIT6_DISP_LH jit (bv #xeb000000 32) (bv #x000d 32) REG_1 REG_1 REG_0 (bv 3 32))
      ; ltg %r1,prog(%b2,%r1)
      ; ARTIFACT: offsetof(struct bpf_array, ptrs) == 8
      (EMIT6_DISP_LH jit (bv #xe3000000 32) (bv #x0002 32) REG_1 BPF_REG_2 REG_1 (bv 8 32))
      ; brc 0x8,out
      (define patch_3_brc (bpf_jit-prg jit))
      (EMIT4_PCREL_RIC jit (bv #xa7040000 32) (bv 8 32) (bpf_jit-prg jit))

      ;
      ; Restore registers before calling function
      ;
      (save_restore_regs jit (bv REGS_RESTORE 32) stack_depth)

      ;
      ; goto *(prog->bpf_func + tail_call_start);
      ;

      ; lg %r1,bpf_func(%r1)
      ; ARTIFACT: offsetof(struct bpf_prog, bpf_func) == 0
      (EMIT6_DISP_LH jit (bv #xe3000000 32) (bv #x0004 32) REG_1 REG_1 REG_0 (bv 0 32))
      ; bc 0xf,tail_call_start(%r1)
      (_EMIT4 jit (bvadd (bv #x47f01000 32) (bpf_jit-tail_call_start jit)))
      ; out:
      (when (bpf_jit-prg_buf jit)
        (copy-to-prg-buf!
          jit
          (bvadd patch_1_clrj (bv 2 32))
          (extract 15 0 (bvashr (bvsub (bpf_jit-prg jit) patch_1_clrj) (bv 1 32))))
        (copy-to-prg-buf!
          jit
          (bvadd patch_2_clij (bv 2 32))
          (extract 15 0 (bvashr (bvsub (bpf_jit-prg jit) patch_2_clij) (bv 1 32))))
        (copy-to-prg-buf!
          jit
          (bvadd patch_3_brc (bv 2 32))
          (extract 15 0 (bvashr (bvsub (bpf_jit-prg jit) patch_3_brc) (bv 1 32)))))]
    [else ; too complex, give up
     (bug #:msg (format "Unknown opcode: ~v" (bpf:insn-code insn)))]))
