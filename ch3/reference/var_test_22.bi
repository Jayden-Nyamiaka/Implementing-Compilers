(X86Program
  (Info2
    (locals_types
      ((v.1 Integer)
       (w.1 Integer)
       (x.1 Integer)
       (y.1 Integer)
       (z.1 Integer)
       ($tmp.1 Integer)))
    (conflicts
      (((VarL $tmp.1)
        ((VarL z.1) (RegL Rsp) (RegL Rax)))
       ((VarL v.1) ((VarL w.1) (RegL Rsp)))
       ((VarL w.1)
        ((VarL v.1)
         (VarL x.1)
         (VarL y.1)
         (VarL z.1)
         (RegL Rsp)))
       ((VarL x.1)
        ((VarL w.1) (VarL y.1) (RegL Rsp)))
       ((VarL y.1)
        ((VarL w.1)
         (VarL x.1)
         (VarL z.1)
         (RegL Rsp)))
       ((VarL z.1)
        ((VarL $tmp.1)
         (VarL w.1)
         (VarL y.1)
         (RegL Rsp)))
       ((RegL Rsp)
        ((VarL $tmp.1)
         (VarL v.1)
         (VarL w.1)
         (VarL x.1)
         (VarL y.1)
         (VarL z.1)
         (RegL Rax)))
       ((RegL Rax) ((VarL $tmp.1) (RegL Rsp))))))
  (((Label start)
    (Block
      Binfo1
      ((Movq (Imm 1) (Var v.1))
       (Movq (Imm 46) (Var w.1))
       (Movq (Var v.1) (Var x.1))
       (Addq (Imm 7) (Var x.1))
       (Movq (Imm 4) (Var y.1))
       (Addq (Var x.1) (Var y.1))
       (Movq (Var x.1) (Var z.1))
       (Addq (Var w.1) (Var z.1))
       (Movq (Var y.1) (Var $tmp.1))
       (Negq (Var $tmp.1))
       (Movq (Var z.1) (Reg Rax))
       (Addq (Var $tmp.1) (Reg Rax))
       (Jmp (Label conclusion)))))))