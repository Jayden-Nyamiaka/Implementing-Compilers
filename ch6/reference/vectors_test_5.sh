(Program
  (Let
    v1
    (Vec ((Int 0)) (Vector (Integer)))
    (Let
      v2
      (Vec ((Int 0)) (Vector (Integer)))
      (If
        (Prim Eq ((Var v1) (Var v2)))
        (Int 777)
        (Int 42)))))
