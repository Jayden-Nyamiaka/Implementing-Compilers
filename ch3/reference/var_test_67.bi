(X86Program
  (Info2
    (locals_types
      ((a.1 Integer)
       (b.1 Integer)
       (c.1 Integer)
       ($tmp.1 Integer)))
    (conflicts
      (((VarL $tmp.1)
        ((VarL b.1) (VarL c.1) (RegL Rsp)))
       ((VarL a.1)
        ((VarL b.1)
         (VarL c.1)
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
       ((VarL b.1)
        ((VarL $tmp.1)
         (VarL a.1)
         (VarL c.1)
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
       ((VarL c.1)
        ((VarL $tmp.1)
         (VarL a.1)
         (VarL b.1)
         (RegL Rsp)
         (RegL Rax)))
       ((RegL Rsp)
        ((VarL $tmp.1)
         (VarL a.1)
         (VarL b.1)
         (VarL c.1)
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
        ((VarL a.1)
         (VarL b.1)
         (VarL c.1)
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
        ((VarL a.1)
         (VarL b.1)
         (RegL Rsp)
         (RegL Rax)))
       ((RegL Rdx)
        ((VarL a.1)
         (VarL b.1)
         (RegL Rsp)
         (RegL Rax)))
       ((RegL Rsi)
        ((VarL a.1)
         (VarL b.1)
         (RegL Rsp)
         (RegL Rax)))
       ((RegL Rdi)
        ((VarL a.1)
         (VarL b.1)
         (RegL Rsp)
         (RegL Rax)))
       ((RegL R8)
        ((VarL a.1)
         (VarL b.1)
         (RegL Rsp)
         (RegL Rax)))
       ((RegL R9)
        ((VarL a.1)
         (VarL b.1)
         (RegL Rsp)
         (RegL Rax)))
       ((RegL R10)
        ((VarL a.1)
         (VarL b.1)
         (RegL Rsp)
         (RegL Rax)))
       ((RegL R11)
        ((VarL a.1)
         (VarL b.1)
         (RegL Rsp)
         (RegL Rax))))))
  (((Label start)
    (Block
      Binfo1
      ((Callq (Label read_int) 0)
       (Movq (Reg Rax) (Var a.1))
       (Callq (Label read_int) 0)
       (Movq (Reg Rax) (Var b.1))
       (Callq (Label read_int) 0)
       (Movq (Reg Rax) (Var c.1))
       (Movq (Var a.1) (Var $tmp.1))
       (Addq (Var b.1) (Var $tmp.1))
       (Movq (Var $tmp.1) (Reg Rax))
       (Addq (Var c.1) (Reg Rax))
       (Jmp (Label conclusion)))))))