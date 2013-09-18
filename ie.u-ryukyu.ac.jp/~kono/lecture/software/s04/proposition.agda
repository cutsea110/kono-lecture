module proposition where

postulate A : Set
postulate B : Set

Lemma1 : Set
Lemma1 = A -> ( A -> B ) -> B

lemma1 : Lemma1
lemma1 a b = b a

-- lemma1 a a-b = a-b a

lemma2 : Lemma1
lemma2 = \a b -> b a

-- lemma1 = \a a-b -> a-b a
-- lemma1 = \a b -> b a
-- lemma1  a b = b a

lemma3 : Lemma1
lemma3 = \a -> ( \b -> b a )

record _∧_ (A B : Set) : Set where
   field 
      and1 : A
      and2 : B

data _∧d_ ( A B : Set ) : Set where
  and : A -> B -> A ∧d B

Lemma4 : Set
Lemma4 = B -> A -> (B ∧ A)

lemma4 : Lemma4
lemma4 = \b -> \a -> record { and1 = b ;  and2 = a }

Lemma5 : Set
Lemma5 = (A ∧ B) -> B

lemma5 : Lemma5
lemma5 = \a -> (_∧_.and2 a)

data _∨_  (A B : Set) : Set where
  or1 : A -> A ∨ B
  or2 : B -> A ∨ B

Lemma6  : Set
Lemma6 = B -> ( A ∨ B )

lemma6 : Lemma6
lemma6 = \b ->  or2 b




