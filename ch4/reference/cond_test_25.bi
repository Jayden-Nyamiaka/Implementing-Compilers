(X86Program
  (Info2
    (locals_types
      (($tmp.1 Integer)
       ($tmp.2 Boolean)
       (x.1 Integer)))
    (conflicts
      (((VarL $tmp.1) ((VarL x.1) (RegL Rsp)))
       ((VarL $tmp.2) ((RegL Rsp)))
       ((VarL x.1)
        ((VarL $tmp.1)
         (RegL Rsp)
         (RegL Rax)
         (RegL Rcx)
         (RegL Rdx)
         (RegL Rsi)
         (RegL Rdi)
         (RegL R8)
         (RegL R9)
         (RegL R10)
         (RegL R11)))
       ((RegL Rsp)
        ((VarL $tmp.1)
         (VarL $tmp.2)
         (VarL x.1)
         (RegL Rax)
         (RegL Rcx)
         (RegL Rdx)
         (RegL Rsi)
         (RegL Rdi)
         (RegL R8)
         (RegL R9)
         (RegL R10)
         (RegL R11)
         (RegL Rflags)))
       ((RegL Rax)
        ((VarL x.1)
         (RegL Rsp)
         (RegL Rcx)
         (RegL Rdx)
         (RegL Rsi)
         (RegL Rdi)
         (RegL R8)
         (RegL R9)
         (RegL R10)
         (RegL R11)))
       ((RegL Rcx)
        ((VarL x.1) (RegL Rsp) (RegL Rax)))
       ((RegL Rdx)
        ((VarL x.1) (RegL Rsp) (RegL Rax)))
       ((RegL Rsi)
        ((VarL x.1) (RegL Rsp) (RegL Rax)))
       ((RegL Rdi)
        ((VarL x.1) (RegL Rsp) (RegL Rax)))
       ((RegL R8)
        ((VarL x.1) (RegL Rsp) (RegL Rax)))
       ((RegL R9)
        ((VarL x.1) (RegL Rsp) (RegL Rax)))
       ((RegL R10)
        ((VarL x.1) (RegL Rsp) (RegL Rax)))
       ((RegL R11)
        ((VarL x.1) (RegL Rsp) (RegL Rax)))
       ((RegL Rflags) ((RegL Rsp))))))
  (((Label block_1)
    (Block
      Binfo1
      ((Movq (Imm 77) (Reg Rax))
       (Jmp (Label conclusion)))))
   ((Label block_2)
    (Block
      Binfo1
      ((Movq (Imm 42) (Reg Rax))
       (Jmp (Label conclusion)))))
   ((Label start)
    (Block
      Binfo1
      ((Movq (Imm 1) (Var x.1))
       (Callq (Label read_int) 0)
       (Movq (Reg Rax) (Var $tmp.1))
       (Cmpq (Var $tmp.1) (Var x.1))
       (Set CC_e (ByteReg Al))
       (Movzbq (ByteReg Al) (Var $tmp.2))
       (Cmpq (Imm 0) (Var $tmp.2))
       (JmpIf CC_e (Label block_1))
       (Jmp (Label block_2)))))))