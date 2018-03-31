TupleVect : (length: Nat) -> Type -> Type
TupleVect Z _ = () 
TupleVect (S k) T = (T, TupleVect k T)

total
appendTV : TupleVect n a -> TupleVect m a -> TupleVect (n + m) a
appendTV () {n=Z} t = t
appendTV (a, b) {n=S(k)} t = (a, appendTV b t)
