(X86Program
  (Info2
    (locals_types
      ((x.1 Integer) (y.1 Unit) (z.1 Unit)))
    (conflicts
      (((VarL x.1)
        ((VarL y.1) (VarL z.1) (RegL Rsp)))
       ((VarL y.1) ((VarL x.1) (RegL Rsp)))
       ((VarL z.1) ((VarL x.1) (RegL Rsp)))
       ((RegL Rsp)
        ((VarL x.1)
         (VarL y.1)
         (VarL z.1)
         (RegL Rax)))
       ((RegL Rax) ((RegL Rsp))))))
  (((Label start)
    (Block
      Binfo1
      ((Movq (Imm 0) (Var x.1))
       (Movq (Imm 0) (Var y.1))
       (Movq (Imm 42) (Var x.1))
       (Movq (Var y.1) (Var z.1))
       (Movq (Var x.1) (Reg Rax))
       (Jmp (Label conclusion)))))))
