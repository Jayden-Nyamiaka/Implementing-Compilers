(CProgram
  (Info (locals_types ()))
  (((Label block_1)
    (Return (Atm (Int 42))))
   ((Label block_2) (Return (Atm (Int 0))))
   ((Label start)
    (IfStmt
      (op Gt)
      (arg1 (Int 42))
      (arg2 (Int 0))
      (jump_then (Label block_1))
      (jump_else (Label block_2))))))
