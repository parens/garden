module Naive where

data Nat : Set where
 z : Nat
 s : Nat -> Nat

data Lt : Nat -> Nat -> Set where
 lt/z : {X : Nat} -> Lt z (s X)
 lt/s : {X Y : Nat} -> Lt X Y -> Lt (s X) (s Y)

data Lte : Nat -> Nat -> Set where
 lte : {X Y : Nat} -> Lt X (s Y) -> Lte X Y


lt_shift : {X Y : Nat} -> Lt X Y -> Lt X (s Y)
lt_shift lt/z = lt/z
lt_shift (lt/s D) = lt/s (lt_shift D)

lt_succ : (X : Nat) -> Lt X (s X)
lt_succ z = lt/z
lt_succ (s X) = lt/s (lt_succ X)

lte_refl : (X : Nat) -> Lte X X
lte_refl X = lte (lt_succ X)

lte_s_of_lt : {X Y : Nat} -> Lt X Y -> Lte (s X) Y
lte_s_of_lt D = lte (lt/s D)

lte_trans_z : {X Y : Nat} -> Lte z X -> Lte X Y -> Lte z Y
lte_trans_z (lte lt/z) (lte (lt/z {Y})) = lte (lt/z {Y})
lte_trans_z (lte lt/z) (lte (lt/s {X}{Y} D)) = lte (lt/z {Y})

lt_absurd : {X Y Z : Nat} -> Lt (s Y) (s z) -> Lte (s X) Z
lt_absurd (lt/s ())

lte_trans : {X Y Z : Nat} -> Lte X Y -> Lte Y Z -> Lte X Z
lte_trans {z} {Y} {Z} (lte lt/z) D2 =  lte_trans_z  (lte lt/z) D2
lte_trans {s X} {s Y} {s Z} (lte (lt/s D1)) (lte (lt/s D2)) with lte_trans (lte D1) (lte D2)
... | lte D = lte (lt/s D)
lte_trans {s X} {z} {Z} (lte D1) (lte D2) = lt_absurd {X} {X} {Z} D1
lte_trans {s _} {s Y} {z} (lte D1) (lte D2) = lt_absurd D2

lt_trans_lte : {X Y Z : Nat} -> Lt X Y -> Lte Y Z -> Lt X Z
lt_trans_lte {z} {s Y} {s Z} lt/z _ = lt/z
lt_trans_lte {s X} {s Y} {s Z} (lt/s D1) (lte (lt/s D2)) with lt_trans_lte D1 (lte D2)
... | D = lt/s D
lt_trans_lte {s X} {z} {Z} () D2
lt_trans_lte {s _} {s Y} {z} ( D1) (lte (lt/s ()))
lt_trans_lte {z} {(s X)} {z} (_) (lte (lt/s ()))
lt_trans_lte {z} {z} {_} () _

lt_trans : {X Y Z : Nat} -> Lt X Y -> Lt Y Z -> Lt X Z
lt_trans {z} {s Y} {s Z} lt/z _ = lt/z
lt_trans {s X} {s Y} {s Z} (lt/s D1) (lt/s D2) with lt_trans D1 D2
... | D = lt/s D
lt_trans {_} {z} {_} () D2
lt_trans {_} {_} {z} _ ()


data _==_ {A : Set} (x : A) :  A -> Set where
  refl :  x == x

data Ord : Nat -> Nat -> Set where
 ord/lt : {X Y : Nat} -> (Lt X Y) -> Ord X Y
 ord/gt : {X Y : Nat} -> (Lt Y X) -> Ord X Y
 ord/eq : {X Y : Nat} -> (X == Y) -> Ord X Y

data Option (A : Set) : Set where
  None : Option A
  Some : (x : A) -> Option A

-- Tree X Y is a tree where all keys are in the interval [X,Y).
-- Thus if X = Y then the tree is empty.
data Tree : Nat -> Nat -> Set where
  Empty : {X : Nat} {Y : Nat} (D : Lte X Y) -> Tree X Y
  Node : {X : Nat} (Y : Nat) {Z : Nat} (D1 : Lte X Y) (D2 : Lt Y Z) (L : Tree X Y) (R : Tree (s Y) Z) -> Tree X Z

sym : {A : Set} {X Y : A} -> X == Y -> Y == X
sym refl = refl

trans : {A : Set} {X Y Z : A} -> X == Y -> Y == Z -> X == Z
trans refl refl = refl

respects : {A B : Set} {X Y : A} (f : A -> B) -> X == Y -> f X == f Y
respects f refl = refl

cmp : (X Y : Nat) -> Ord X Y
cmp z z = ord/eq refl
cmp (s _) z = ord/gt lt/z
cmp z (s _) = ord/lt lt/z
cmp (s X) (s Y) with cmp X Y
... | ord/eq D = ord/eq (respects s D)
... | ord/lt D = ord/lt (lt/s D)
... | ord/gt D = ord/gt (lt/s D)

t = Node (s z)
    (lte (lt/s lt/z))
    (lt/s (lt/z {z}))
    (Empty {s z} {s z} (lte (lt/s (lt/z {z}))))
    (Empty {s (s z)} {s (s z)} (lte (lt/s (lt/s (lt/z {z})))))

data Mem : {X Y : Nat} -> Tree X Y -> Nat -> Set where
  mem/here : {X Y Z : Nat} {D1 : Lte X Y} {D2 : Lt Y Z}
    {L : Tree X Y} {R : Tree (s Y) Z} ->
    Mem (Node Y D1 D2 L R) X
  mem/left : {X V Z Y : Nat} {D1 : Lte X V} {D2 : Lt V Z}
    {L : Tree X V} {R : Tree (s V) Z} ->
    Mem L Y ->
    Mem (Node V D1 D2 L R) Y
  mem/right : {X V Z Y : Nat} {D1 : Lte X V} {D2 : Lt V Z}
    {L : Tree X V} {R : Tree (s V) Z} ->
    Mem R Y ->
    Mem (Node V D1 D2 L R) Y

tmin : Nat -> Nat -> Nat
tmin X Y with cmp X Y
... | ord/lt D = X
... | ord/eq D = X
... | ord/gt D = Y

tmax : Nat -> Nat -> Nat
tmax X Y with cmp X Y
... | ord/lt D = Y
... | ord/eq D = (s X)
... | ord/gt D = (s X)


cmp_lt : {V Z : Nat} -> (D : Lt V Z) -> (cmp V Z == ord/lt D)
cmp_lt {z} {s X} lt/z  = refl
cmp_lt {s X} {s Y} (lt/s D) with cmp X Y | cmp_lt {X} {Y} D
cmp_lt {s X} {s Y} (lt/s D) | .(ord/lt D) | refl = refl


remax' : {X Y : Nat} -> Lt X Y -> tmax X Y == Y
remax' {X} {Y} D with cmp X Y | cmp_lt D
... | .(ord/lt D) | refl = refl

remax : {X Y Z : Nat} -> Lt Y Z -> Tree X Z -> Tree X (tmax Y Z)
remax {X} {Y} {Z} D T with tmax Y Z | remax' D
... | .Z | refl = T

unmax : {X Y Z : Nat} -> Lt Y Z ->  Tree X (tmax Y Z) -> Tree X Z
unmax {X} {Y} {Z} D T with tmax Y Z | remax' D
... | .Z | refl = T

data False : Set where

bot-elim : {P : Set} -> False -> P
bot-elim ()

lt_lte_contra : {P : Set} {X Y : Nat} -> Lt X (s Y) -> Lt Y X -> P
lt_lte_contra {P} {z} {_} _ ()
lt_lte_contra {P} {s _} {z} (lt/s () ) lt/z
lt_lte_contra {P} {s X} {s Y} (lt/s D) (lt/s D') = lt D lte D' contra

remin' : {X Y : Nat} -> Lte X Y -> tmin Y X == X
remin' {X} {Y} (lte D) with cmp Y X
remin' {X} {Y} (lte D) | ord/lt LT = lt D lte LT contra
remin' {X} {Y} (lte D) | ord/eq EQ with X
remin' {X} {Y} (lte D) | ord/eq refl | .Y = refl
remin' {X} {Y} (lte D) | ord/gt GT  = refl


remin : {X Y Z : Nat} -> Lte X Y -> Tree X Z -> Tree (tmin Y X) Z
remin {X} {Y} {Z} D T with tmin Y X | remin' D
... | .X | refl = T

remin'' : {X Y : Nat} -> Lt X Y -> tmin Y (s X) == (s X)
remin'' {X} {Y} (D) with cmp Y (s X)
remin'' {X} {Y} (D) | ord/lt LT = lt_lte_contra LT D
remin'' {X} {Y} (D) | ord/gt GT = refl
remin'' {X} {Y} (D) | ord/eq EQ = EQ

unmin : {X V Y : Nat} -> Lt X V ->  Tree (tmin V (s X)) Y -> Tree (s X) Y
unmin {X} {V} {Y} D T with  tmin V (s X) | remin'' {X} {V} D
... | .(s X) | refl = T


lte_of_lt : {X Y : Nat} -> Lt X Y -> Lte X Y
lte_of_lt D = lte (lt_shift D)

tmax_lte : (X Y : Nat) -> Lte Y (tmax X Y)
tmax_lte X Y with cmp X Y
tmax_lte X Y | ord/lt D = lte_refl Y
tmax_lte X Y | ord/eq D with X
tmax_lte X Y | (ord/eq refl) | .Y = lte (lt_shift (lt_succ Y))
tmax_lte X Y | ord/gt D = lte lt lt D shift shift

tmin_lte : (V X : Nat) -> Lte (tmin V X) V
tmin_lte V X with cmp V X
... | ord/lt D = lte_refl V
... | ord/eq D = lte_refl V
... | ord/gt D = lte (lt_shift D)

tmin_lte_r : (V X : Nat) -> Lte (tmin V X) X
tmin_lte_r V X with cmp V X
tmin_lte_r V X | ord/lt D = lte (lt_shift D)
tmin_lte_r V X | ord/eq D with V
tmin_lte_r V X | ord/eq refl | .X = lte_refl X
tmin_lte_r V X | ord/gt D = lte_refl X


tmax_lt : (V X : Nat) -> Lt V (tmax V X)
tmax_lt V X with cmp V X
... | ord/lt D = D
... | ord/eq D = lt_succ V
... | ord/gt D = lt_succ V

--(lte_trans (tmin_lte V X) (lte_of_lt D)))
insert : {X Z : Nat} -> Tree X Z -> (V : Nat) -> Tree (tmin V X) (tmax V Z)
insert {X} {Z} (Empty D) V = Node V (tmin_lte V X) (tmax V lt Z)
                               (Empty {tmin V X} {V} (tmin_lte V  X)) (Empty {s V} {tmax V Z} (lte_s_of_lt (tmax V lt Z)))
insert {X} {Z} (Node Y D1 D2 L R) V with cmp V Y
insert {X} {Z} (Node Y D1 D2 L R) V | ord/lt D = Node Y ((lte_trans (tmin_lte V X) (lte_of_lt D)))
                        (lt_trans_lte D2 (tmax_lte V Z))
                        (unmax D (insert {X} {Y} L V))
                        (remax (lt_trans D D2) R)
insert {X} {Z} (Node Y D1 D2 L R) V | ord/gt D =
    Node Y (lte_trans (tmin_lte_r V X) D1) (lt D trans (tmax V lt Z)) (remin {X} {V} {Y} (lte_trans  D1 (lte_of_lt D)) L) (unmin D (insert {s Y} {Z} R V))
-- want Tree (s Y) (tmax V Z | cmp V Z)
-- have Tree (tmin V (s Y) | cmp V (s Y)) (tmax V Z | cmp V Z)
insert {X} {Z} (Node Y D1 D2 L R) V | ord/eq D with V
insert {X} {Z} (Node Y D1 D2 L R) V | ord/eq refl | .Y = (remin D1 (remax D2 (Node Y D1 D2 L R)))
