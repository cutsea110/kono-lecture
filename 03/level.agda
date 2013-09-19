module level where

postulate A : Set
postulate B : Set
postulate C : Set
postulate a : A
postulate b : A
postulate c : A

{--
infixr 40 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A -> List A -> List A

l1 = a ∷ []

-- l1' = A ∷ [] -- error!
--}

{--
open import Level

infixr 40 _∷_
data List (A : Set (suc zero)) : Set (suc zero) where
  [] : List A
  _∷_ : A -> List A -> List A

-- l1 = a ∷ [] -- error!

l1' = A ∷ []
--}


open import Level

infixr 40 _∷_
data List {a} (A : Set a) : Set a where
  [] : List A
  _∷_ : A -> List A -> List A
infixl 30 _++_
_++_ : ∀ {a} {A : Set a} -> List A -> List A -> List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

l1 = a ∷ []
l1' = A ∷ []
l2 = a ∷ b ∷ a ∷ c ∷ []
l3 = l1 ++ l2
infixr 20 _==_
data _==_ {n} {A : Set n} : List A -> List A -> Set n where
  reflection : {x : List A} -> x == x
  eq-cons : {x y : List A} {a : A} -> x == y -> (a ∷ x) == (a ∷ y)
  trans-list : {x y z : List A} {a : A} -> x == y -> y == z -> x == z

list-id-l : {A : Set} -> {x : List A} -> [] ++ x == x
list-id-l = reflection
