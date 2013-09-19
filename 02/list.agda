module list where

open import Data.List

postulate A : Set
postulate a : A
postulate b : A
postulate c : A

l1 = [ a ]
l2 = a ∷ b ∷ c ∷ []
l3 = l1 ++ l2

infixr 20 _==_
data _==_ {n} {A : Set n} : List A -> List A -> Set n where
  reflection : {x : List A} -> x == x

list-id-l : {A : Set} -> {x : List A} -> ([] ++ x) == x
list-id-l = reflection

open import Relation.Binary.PropositionalEquality

==-to-≡ : {A : Set} -> {x y : List A} -> x == y -> x ≡ y
==-to-≡ reflection = refl

cong1 : {A : Set} {B : Set} -> (f : List A -> List B) -> {x : List A} -> {y : List A} -> x == y -> f x == f y
cong1 f reflection = reflection
eq-cons : {A : Set} {x y : List A} (a : A) -> x == y -> (a ∷ x) == (a ∷ y)
eq-cons a eq = cong1 (_∷_ a) eq
trans-list : {A : Set} {x y z : List A} -> x == y -> y == z -> x == z
trans-list reflection reflection = reflection

