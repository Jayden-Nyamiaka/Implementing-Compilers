(X86Program
  (Info2
    (locals_types
      ((x.1 Integer)
       (y.1 Integer)
       (z.1 Integer)
       (w.1 Integer)))
    (conflicts
      (((VarL w.1)
        ((VarL x.1) (VarL z.1) (RegL Rsp)))
       ((VarL x.1)
        ((VarL w.1)
         (VarL y.1)
         (VarL z.1)
         (RegL Rsp)
         (RegL Rax)))
       ((VarL y.1) ((VarL x.1) (RegL Rsp)))
       ((VarL z.1)
        ((VarL w.1) (VarL x.1) (RegL Rsp)))
       ((RegL Rsp)
        ((VarL w.1)
         (VarL x.1)
         (VarL y.1)
         (VarL z.1)
         (RegL Rax)))
       ((RegL Rax) ((VarL x.1) (RegL Rsp))))))
  (((Label start)
    (Block
      Binfo1
      ((Movq (Imm 10) (Var x.1))
       (Movq (Imm 15) (Var y.1))
       (Movq (Var y.1) (Var z.1))
       (Addq (Var y.1) (Var z.1))
       (Movq (Imm 2) (Var w.1))
       (Addq (Var z.1) (Var w.1))
       (Movq (Var w.1) (Reg Rax))
       (Addq (Var x.1) (Reg Rax))
       (Jmp (Label conclusion)))))))