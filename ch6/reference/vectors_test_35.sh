(Program
  (Let
    v
    (Vec ((Int 0)) (Vector (Integer)))
    (Let
      void
      (VecSet (Var v) 0 (Int 21))
      (Prim Add ((Int 21) (VecRef (Var v) 0))))))
