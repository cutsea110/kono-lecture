module record-type where

data _∨_ (A B : Set) : Set where
  or1 : A -> A ∨ B
  or2 : B -> A ∨ B

postulate A B C : Set
postulate a1 a2 a3 : A
postulate b1 b2 b3 : B
x : A ∨ B
x = or1 a1
y : A ∨ B
y = or2 b1
f : A ∨ B -> A
f (or1 a) = a
f (or2 b) = a1

record _∧_ (A B : Set) : Set where
  field
    and1 : A
    and2 : B
z : A ∧ B
z = record { and1 = a1 ; and2 = b2 }
xa : A
xa = _∧_.and1 z
xb : B
xb = _∧_.and2 z

open _∧_
ya : A
ya = and1 z

--------

open import Relation.Binary.PropositionalEquality

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

record Mod3 (m : Nat) : Set where
  field
    mod3 : (suc (suc (suc m))) ≡ m
  n : Nat
  n = m

open Mod3
Lemma1 : {m : Nat} -> (x : Mod3 (suc (suc (suc m)))) (y : Mod3 m) -> n x ≡ n y
Lemma1 x y = mod3 y

postulate mx : Mod3 (suc zero)
postulate my : Mod3 (suc (suc (suc (suc zero))))
postulate mz : Mod3 (suc (suc (suc (suc (suc (suc (suc zero)))))))
foo = Lemma1 my mx
bar = Lemma1 mz my
-- quz = Lemma1 mz mx -- Error!

postulate nx : Mod3 zero
postulate ny : Mod3 (suc (suc (suc zero)))
postulate nz : Mod3 (suc (suc (suc (suc (suc (suc zero))))))
foo' = Lemma1 ny nx
bar' = Lemma1 nz ny
-- quz' = Lemma1 nz nx --Error!


