module proposition where

postulate A : Set
postulate B : Set

Lemma1 : Set
Lemma1 = A -> (A -> B) -> B

lemma1 : Lemma1
-- lemma1 a a-b = a-b a
-- lemma1 = \a a-b -> a-b a
-- lemma1 = \a b -> b a
lemma1 a b = b a

-- product

record _∧_ (A B : Set) : Set where
  field
    and1 : A
    and2 : B

lemma4 : A -> B -> A ∧ B
lemma4 = \b -> \a -> record { and1 = b ; and2 = a }

lemma5 : A ∧ B -> B
-- lemma5 = \b -> _∧_.and2 b
lemma5 = _∧_.and2

-- disjuncion

data _∨_ (A B : Set) : Set where
  or1 : A -> A ∨ B
  or2 : B -> A ∨ B

Lemma6 : Set
Lemma6 = B -> A ∨ B
lemma6 : Lemma6
-- lemma6 = \b -> or2 b
lemma6 = or2

lemma7 : A ∨ A -> A
lemma7 (or1 a) = a
lemma7 (or2 b) = b

-- issue 4.1
