(X86Program
  (Info2
    (locals_types
      (($ea.1 (Vector (Integer)))
       ($tmp.1 Integer)
       ($tmp.2 Integer)
       ($tmp.3 Integer)
       (_.1 Unit)
       (_.2 Unit)
       (v.1 (Vector (Integer)))))
    (conflicts
      (((VarL $ea.1)
        ((VarL _.1) (RegL Rsp) (RegL R11)))
       ((VarL $tmp.1) ((RegL Rsp) (RegL R15)))
       ((VarL $tmp.2)
        ((VarL $tmp.3) (RegL Rsp) (RegL R15)))
       ((VarL $tmp.3)
        ((VarL $tmp.2) (RegL Rsp) (RegL R15)))
       ((VarL _.1)
        ((VarL $ea.1) (VarL v.1) (RegL Rsp)))
       ((VarL _.2) ((RegL Rsp)))
       ((VarL v.1)
        ((VarL _.1) (RegL Rsp) (RegL R11)))
       ((RegL Rsp)
        ((VarL $ea.1)
         (VarL $tmp.1)
         (VarL $tmp.2)
         (VarL $tmp.3)
         (VarL _.1)
         (VarL _.2)
         (VarL v.1)
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
       ((RegL Rax) ((RegL Rsp)))
       ((RegL Rcx) ((RegL Rsp)))
       ((RegL Rdx) ((RegL Rsp)))
       ((RegL Rsi) ((RegL Rsp) (RegL Rdi)))
       ((RegL Rdi) ((RegL Rsp) (RegL Rsi)))
       ((RegL R8) ((RegL Rsp)))
       ((RegL R9) ((RegL Rsp)))
       ((RegL R10) ((RegL Rsp)))
       ((RegL R11)
        ((VarL $ea.1) (VarL v.1) (RegL Rsp)))
       ((RegL R15)
        ((VarL $tmp.1)
         (VarL $tmp.2)
         (VarL $tmp.3)
         (RegL Rflags)))
       ((RegL Rflags) ((RegL Rsp) (RegL R15))))))
  (((Label block_1)
    (Block
      Binfo1
      ((Movq
         (GlobalArg (Label free_ptr))
         (Reg R11))
       (Addq
         (Imm 16)
         (GlobalArg (Label free_ptr)))
       (Movq (Imm 3) (Deref R11 0))
       (Movq (Reg R11) (Var $ea.1))
       (Movq (Var $ea.1) (Reg R11))
       (Movq (Imm 777) (Deref R11 8))
       (Movq (Imm 0) (Var _.1))
       (Movq (Var $ea.1) (Var v.1))
       (Movq (Var v.1) (Reg R11))
       (Movq (Imm 42) (Deref R11 8))
       (Movq (Imm 0) (Var _.1))
       (Movq (Var v.1) (Reg R11))
       (Movq (Deref R11 8) (Reg Rax))
       (Jmp (Label conclusion)))))
   ((Label block_2)
    (Block
      Binfo1
      ((Movq (Imm 0) (Var _.2))
       (Jmp (Label block_1)))))
   ((Label block_3)
    (Block
      Binfo1
      ((Movq (Reg R15) (Reg Rdi))
       (Movq (Imm 16) (Reg Rsi))
       (Callq (Label collect) 2)
       (Jmp (Label block_1)))))
   ((Label start)
    (Block
      Binfo1
      ((Movq
         (GlobalArg (Label free_ptr))
         (Var $tmp.1))
       (Movq (Var $tmp.1) (Var $tmp.2))
       (Addq (Imm 16) (Var $tmp.2))
       (Movq
         (GlobalArg (Label fromspace_end))
         (Var $tmp.3))
       (Cmpq (Var $tmp.3) (Var $tmp.2))
       (JmpIf CC_l (Label block_2))
       (Jmp (Label block_3)))))))
