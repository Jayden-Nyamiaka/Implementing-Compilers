(CProgram
  (Info (locals_types ()))
  (((Label start)
    (Seq
      (Assign x.1 (Atm (Bool true)))
      (IfStmt
        (op Eq)
        (arg1 (Var x.1))
        (arg2 (Bool true))
        (jump_then (Label block_5))
        (jump_else (Label block_4)))))
   ((Label block_4)
    (Seq
      (Assign x.2 (Atm (Bool false)))
      (Goto (Label block_3))))
   ((Label block_5)
    (Seq
      (Assign x.2 (Atm (Bool true)))
      (Goto (Label block_3))))
   ((Label block_3)
    (IfStmt
      (op Eq)
      (arg1 (Var x.2))
      (arg2 (Bool true))
      (jump_then (Label block_1))
      (jump_else (Label block_2))))
   ((Label block_1)
    (Return (Atm (Int 42))))
   ((Label block_2)
    (Return (Atm (Int 777))))))
