(CProgram
  (Info (locals_types ()))
  (((Label start)
    (IfStmt
      (op Eq)
      (arg1 (Int 1))
      (arg2 (Int 2))
      (jump_then (Label block_1))
      (jump_else (Label block_2))))
   ((Label block_1)
    (Return (Atm (Int 777))))
   ((Label block_2)
    (Return (Atm (Int 42))))))
