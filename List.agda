module List where

data _==_ {A : Set} (x : A) :  A -> Set where
  refl : x == x

data _OR_ (A B : Set) : Set where
  inl : A -> A OR B
  inr : B -> A OR B


data Nat : Set where
 z : Nat
 s : Nat -> Nat

data Lte : Nat -> Nat -> Set where
  lte/z : {X : Nat} -> Lte z X
  lte/s : {X : Nat} {Y : Nat} -> Lte X Y -> Lte (s X) (s Y)

data List : Nat -> Set where
  nil : {ListBound : Nat} -> List ListBound
  cons : {TailBound : Nat} -> (ListHead : Nat) -> List TailBound -> Lte ListHead TailBound -> List ListHead

data SortedList : Set where
  sl : {X : Nat} -> List X -> SortedList

data UnsortedList : Set where
  unil : UnsortedList
  ucons : Nat -> UnsortedList -> UnsortedList

min : Nat -> Nat -> Nat
min z X = z
min X z = z
min (s X) (s Y) = s (min X Y)

minz : (x : Nat) -> min x z == z
minz z = refl
minz (s X) with min X z | minz X
... | .z | refl = refl

min_either : (X Y : Nat) -> (min X Y == X) OR (min X Y == Y)
min_either z _ = inl refl
min_either X z = inr (minz X)
min_either (s X) (s Y) with min X Y | min_either X Y
... | .X | inl refl = inl refl
... | .Y | inr refl = inr refl

data Cmp : Nat -> Nat -> Set where
  cmp/lte : {X : Nat} {Y : Nat} -> Lte X Y -> Cmp X Y
  cmp/gte : {X : Nat} {Y : Nat} -> Lte Y X -> Cmp X Y

cmp : (X : Nat) (Y : Nat) -> Cmp X Y
cmp z X = cmp/lte lte/z
cmp X z = cmp/gte lte/z
cmp (s X) (s Y) with cmp X Y
... | cmp/lte D = cmp/lte (lte/s D)
... | cmp/gte D = cmp/gte (lte/s D)


respects : {A B : Set} {X Y : A} (f : A -> B) -> X == Y -> f X == f Y
respects f refl = refl


cmp_min : {X : Nat} {Y : Nat} -> Lte X Y -> (min X Y == X)
cmp_min {z} {Y} lte/z = refl
cmp_min {s XX} {s YY} (lte/s D) with cmp_min {XX} {YY} D
... | D1 = respects s D1

cmp_min2 : {X : Nat} {Y : Nat} -> Lte Y X -> (min X Y == Y)
cmp_min2 {X} {z} lte/z = minz X
cmp_min2 {s XX} {s YY} (lte/s D) with cmp_min2 {XX} {YY} D
... | D1 = respects s D1

sym : {X Y : Nat} -> X == Y -> Y == X
sym refl = refl

min_refl : (X : Nat) -> (min X X) == X
min_refl z = refl
min_refl (s X) with min X X | min_refl X
... | .X | refl = refl

lte_refl : (X : Nat) -> Lte X X
lte_refl z = lte/z
lte_refl (s X) = lte/s (lte_refl X)

insert_lte_lem : (X : Nat) -> Lte X (min X X)
insert_lte_lem X with min X X | min_refl X
... | .X | refl = lte_refl X

min_combo : (X Y Z : Nat) -> (XY : Lte X Y) -> (XZ : Lte X Z) -> Lte X (min Y Z)
min_combo X Y Z XY XZ with min Y Z | min_either Y Z
... | .Y | inl refl = XY
... | .Z | inr refl = XZ

insert : {Y : Nat} (X : Nat) -> List Y -> List (min X Y)
insert X nil = nil
insert X (cons Y XS D) with cmp X Y
insert X (cons Y XS D) | cmp/lte LTE with min X Y | cmp_min LTE
insert X (cons Y XS D) | cmp/lte LTE | .X | refl = cons X (cons Y XS D) LTE
insert X (cons Y XS D) | cmp/gte GTE with min X Y | cmp_min2 GTE | lte_refl Y
insert X (cons {TailBound} Y XS D) | cmp/gte GTE | .Y | refl | LTE = cons Y (insert X XS) (min_combo Y X TailBound GTE D)


isort : UnsortedList -> SortedList
isort unil = sl {z} nil
isort (ucons UHead UTail) with isort UTail
... | sl STail = sl (insert UHead STail)
