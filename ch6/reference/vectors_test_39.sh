(Program
  (Let
    v
    (Vec
      ((Vec ((Int 0)) (Vector (Integer))))
      (Vector ((Vector (Integer)))))
    (Let
      v2
      (Vec ((Int 21)) (Vector (Integer)))
      (Begin
        ((VecSet (Var v) 0 (Var v2)))
        (Let
          v3
          (VecRef (VecRef (Var v) 0) 0)
          (Prim Add ((Var v3) (Var v3))))))))
