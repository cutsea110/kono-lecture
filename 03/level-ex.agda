module level-ex where

open import Level

postulate ℓ : Level
postulate A : Set ℓ
postulate a : A
lemma1 : Set ℓ -> A
lemma1 = \x -> a
lemma2 : A -> Set ℓ
lemma2 = \x -> A
lemma3 : Set (suc ℓ)
lemma3 = A -> Set ℓ


{--
-- Heterogeneous binary relations
REL : ∀ {a b} -> Set a -> Set b -> (ℓ : Level) -> Set (a ⊔ b ⊔ ℓ)
REL A B ℓ = A -> B -> Set ℓ -- error!

-- Homogeneous binary relations
Rel : ∀ {a} -> Set a -> (ℓ : Level) -> Set (a ⊔ suc ℓ)
Rel A ℓ = REL A A ℓ
--}
