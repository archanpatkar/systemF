// WIP
// (\x:@X.X->X. x [@X. X->X] x) (?a. \x:a. x)
// let Pair = (?t1. ?t2. \x:t1. \y:t2. ?r. \f:t1->t2->r. f x y)
// (Pair [number] [number] 10 20) [number] (\x:number. \y:number. x)
// let fst = (?t1. ?t2. \x:@R. (t1->t2->R)->R. x [t1] (\e1:t1. \e2:t2. e1))
// (fst [number] [number]) ps1
// let snd = (?t1. ?t2. \x:@R. (t1->t2->R)->R. x [t2] (\e1:t1. \e2:t2. e2))
// (snd [number] [number]) ps1
// (Pair [number] [number] 10 20)
// let id = (?t. \x:t. x)
// id [int] 10
// id [int] 10
// (?a. \x:a->a. x) [int->int]
// (\x:int->int. x 3) (\x:int. x + 10)

// let inl = (?t1. ?t2. \v:t1. ?r. \b1:t1->r. \b2:t2->r. b1 v)
// let inr = (?t1. ?t2. \v:t2. ?r. \b1:t1->r. \b2:t2->r. b2 v)
// let case = (?t1. ?t2. ?j. \v:@r.(t1->r)->(t2->r)->r. \b1:t1->j. \b2:t2->j. v [j] b1 b2)
//  (case [number] [bool] [number]) (inl [number] [bool] 10) (\x:number. x * 2) (\x:bool. 0)
// (case [number] [bool] [bool]) (inr [number] [bool] true) (\x:number. not true) (\x:bool. x)