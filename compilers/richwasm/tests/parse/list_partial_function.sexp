(((Fun (empty)
        (((Qual () ()) (Qual () ((QualV 0))) (Size () ())
          (Type (QualV 0) (SizeV 0) Heapable))
         (()
          (((Rec (QualV 1)
             ((ExLoc
               ((Ref W (LocV 0)
                 (Variant
                  ((Unit (QualC Unr))
                   ((Prod (((Var 0) (QualV 0)) ((Var 0) (QualV 1)))) (QualV 1)))))
                (QualV 1)))
              (QualV 1)))
            (QualV 1)))))
        ()
        ((IVal Unit)
            (IVariantMalloc 0
          ((Unit (QualC Unr))
           ((Prod
             (((Var 0) (QualV 0))
              ((Rec (QualV 1)
                ((ExLoc
                  ((Ref W (LocV 0)
                    (Variant
                     ((Unit (QualC Unr))
                      ((Prod (((Var 0) (QualV 0)) ((Var 0) (QualV 1))))
                       (QualV 1)))))
                   (QualV 1)))
                 (QualV 1)))
               (QualV 1))))
            (QualV 1)))
          (QualV 1))
         (IRecFold
          (Rec (QualV 1)
           ((ExLoc
             ((Ref W (LocV 0)
               (Variant
                ((Unit (QualC Unr))
                 ((Prod (((Var 0) (QualV 0)) ((Var 0) (QualV 1)))) (QualV 1)))))
              (QualV 1)))
            (QualV 1))))
            ))
    (Fun (cons)  
        (((Qual () ()) (Qual () ((QualV 0))) (Size () ())
          (Type (QualV 0) (SizeV 0) Heapable))
         ((((Rec (QualV 1)
             ((ExLoc
               ((Ref W (LocV 0)
                 (Variant
                  ((Unit (QualC Unr))
                   ((Prod (((Var 0) (QualV 0)) ((Var 0) (QualV 1)))) (QualV 1)))))
                (QualV 1)))
              (QualV 1)))
            (QualV 1))
           ((Var 0) (QualV 0)))
          (((Rec (QualV 1)
             ((ExLoc
               ((Ref W (LocV 0)
                 (Variant
                  ((Unit (QualC Unr))
                   ((Prod (((Var 0) (QualV 0)) ((Var 0) (QualV 1)))) (QualV 1)))))
                (QualV 1)))
              (QualV 1)))
            (QualV 1)))))
        () 
        (
            (IGet_local 1 (QualV 0) ((Var 0) (QualV 0)))
        ))
    ) () () )