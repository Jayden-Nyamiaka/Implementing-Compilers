(X86Program
  (Info2
    (locals_types ((x.1 Integer)))
    (conflicts
      (((VarL x.1) ((RegL Rsp)))
       ((RegL Rsp) ((VarL x.1) (RegL Rax)))
       ((RegL Rax) ((RegL Rsp))))))
  (((Label start)
    (Block
      Binfo1
      ((Movq (Imm 40) (Var x.1))
       (Movq (Var x.1) (Reg Rax))
       (Addq (Imm 2) (Reg Rax))
       (Jmp (Label conclusion)))))))
