(CProgram
  (Info
    (locals_types
      (($tmp.1 Integer)
       ($tmp.10 Integer)
       ($tmp.2 Integer)
       ($tmp.3 Integer)
       ($tmp.4 Integer)
       ($tmp.5 Integer)
       ($tmp.6 Integer)
       ($tmp.7 Integer)
       ($tmp.8 Integer)
       ($tmp.9 Integer)
       (x.1 Integer)
       (y.1 Integer))))
  (((Label start)
    (Seq
      (Assign x.1 (Atm (Int 30)))
      (Seq
        (Assign y.1 (Atm (Int 20)))
        (Seq
          (Assign $tmp.1 (Atm (Var x.1)))
          (Seq
            (Assign $tmp.2 (Prim Read ()))
            (Seq
              (Assign
                x.1
                (Prim Sub ((Var $tmp.1) (Var $tmp.2))))
              (Seq
                (Assign $tmp.3 (Atm (Int 0)))
                (Seq
                  (Assign $tmp.4 (Atm (Var y.1)))
                  (Seq
                    (Assign $tmp.5 (Prim Read ()))
                    (Seq
                      (Assign
                        y.1
                        (Prim Add ((Var $tmp.4) (Var $tmp.5))))
                      (Seq
                        (Assign $tmp.6 (Atm (Int 0)))
                        (Seq
                          (Assign
                            $tmp.7
                            (Prim Add ((Var $tmp.3) (Var $tmp.6))))
                          (Seq
                            (Assign $tmp.8 (Atm (Var x.1)))
                            (Seq
                              (Assign $tmp.9 (Atm (Var y.1)))
                              (Seq
                                (Assign
                                  $tmp.10
                                  (Prim Add ((Var $tmp.8) (Var $tmp.9))))
                                (Return
                                  (Prim Add ((Var $tmp.7) (Var $tmp.10)))))))))))))))))))))
