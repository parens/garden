module Naive where

data Nat : Set where
 z : Nat
 s : Nat -> Nat

data Lt : Nat -> Nat -> Set where
 lt/z : {X : Nat} -> Lt z (s X)
 lt/s : {X Y : Nat} -> Lt X Y -> Lt (s X) (s Y)

data _==_ {A : Set} : A -> A -> Set where
  refl : {x : A} -> x == x

data Ord : Nat -> Nat -> Set where
 ord/lt : {X Y : Nat} -> (Lt X Y) -> Ord X Y
 ord/gt : {X Y : Nat} -> (Lt Y X) -> Ord X Y
 ord/eq : {X Y : Nat} -> (X == Y) -> Ord X Y

data Option (A : Set) : Set where
  None : Option A
  Some : (x : A) -> Option A

-- Tree X Y is a tree where all keys are in the interval (X,Y).
-- Thus if X = Y then the tree is empty.
data Tree : Nat -> Nat -> Set where
  Empty : {X : Nat} {Y : Nat} -> Tree X Y
  Node : (X : Nat) {Y : Nat} {Z : Nat} (D1 : Lt Y X) (D2 : Lt X Z) (L : Tree Y X) (R : Tree X Z) -> Tree X Z

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
    lt/z
    (lt/s (lt/z {s z}))
    Empty
    Empty

data Mem : {X Y : Nat} -> Tree X Y -> Nat -> Set where
  mem/here : {X Y Z : Nat} {D1 : Lt X Y} {D2 : Lt Y Z}
    {L : Tree X Y} {R : Tree Y Z} ->
    Mem (Node Y D1 D2 L R) X
  mem/left : {X V Z Y : Nat} {D1 : Lt X V} {D2 : Lt V Z}
    {L : Tree X V} {R : Tree V Z} ->
    Mem L Y ->
    Mem (Node V D1 D2 L R) Y
  mem/right : {X V Z Y : Nat} {D1 : Lt X V} {D2 : Lt V Z}
    {L : Tree X V} {R : Tree V Z} ->
    Mem R Y ->
    Mem (Node V D1 D2 L R) Y

insert : {X Y : Nat} -> Tree X Y -> (V : Nat) -> Tree X Y
insert Empty V = Node V lt/z lt/z Empty Empty
insert {X} (Node .X D1 D2 L R) V with cmp V X
... | ord/lt x = Node X D1 D2 (insert L V) {!R!}
... | ord/gt x = {!Node X D1 D2 L (insert R V) {}!}
... | ord/eq x = (Node X D1 D2 L R)
