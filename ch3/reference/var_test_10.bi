(X86Program
  (Info2
    (locals_types
      ((x.1 Integer)
       (y.1 Integer)
       ($tmp.1 Integer)))
    (conflicts
      (((VarL $tmp.1)
        ((VarL x.1) (RegL Rsp) (RegL Rax)))
       ((VarL x.1)
        ((VarL $tmp.1)
         (VarL y.1)
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
       ((VarL y.1) ((VarL x.1) (RegL Rsp)))
       ((RegL Rsp)
        ((VarL $tmp.1)
         (VarL x.1)
         (VarL y.1)
         (RegL Rax)
         (RegL Rcx)
         (RegL Rdx)
         (RegL Rsi)
         (RegL Rdi)
         (RegL R8)
         (RegL R9)
         (RegL R10)
         (RegL R11)))
       ((RegL Rax)
        ((VarL $tmp.1)
         (VarL x.1)
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
        ((VarL x.1) (RegL Rsp) (RegL Rax))))))
  (((Label start)
    (Block
      Binfo1
      ((Callq (Label read_int) 0)
       (Movq (Reg Rax) (Var x.1))
       (Callq (Label read_int) 0)
       (Movq (Reg Rax) (Var y.1))
       (Movq (Var y.1) (Var $tmp.1))
       (Negq (Var $tmp.1))
       (Movq (Var x.1) (Reg Rax))
       (Addq (Var $tmp.1) (Reg Rax))
       (Jmp (Label conclusion)))))))
