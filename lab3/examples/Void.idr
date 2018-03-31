
loop : Void
loop = loop

total
nohead : Void
nohead = getHead []
  where
    getHead : List Void -> Void
    getHead (x :: xs) = x
