module list-nat where


postulate a : Set
postulate b : Set
postulate c : Set


infixr 40 _::_
data  List {a} (A : Set a)  : Set a where
   [] : List A
   _::_ : A -> List A -> List A


infixl 30 _++_
_++_ : ∀ {a}  {A : Set a } -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data Nat : Set where
   zero : Nat
   suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

_-_ : Nat -> Nat -> Nat
zero - _ = zero
m - zero = m
suc n - suc m = n - m

nlist : ∀ {a} { A : Set a } -> A -> Nat -> List A
nlist h zero = []
nlist h (suc n) = h :: ( nlist h n )

fmap : ∀ {a b} {A : Set a} {B : Set b} -> ( A -> B) -> List A -> List B
fmap _ [] = []
fmap f ( x :: xs ) = (f x) :: fmap f xs

l1 = a :: []
l2 = a :: b :: a :: c ::  []

l3 = l2 ++ l1 ++ l2


open  import  Relation.Binary.PropositionalEquality
open ≡-Reasoning

nat-nlist : {A B : Set} ( h : A ) -> ( f : A -> B ) -> (n : Nat) -> fmap f ( nlist h n ) ≡ nlist ( f h ) n
nat-nlist  h f zero = begin  -- to prove fmap f ( nlist h zero )  ≡ nlist ( f h ) zero
        fmap f ( nlist h zero )
   ≡⟨ refl ⟩
        nlist ( f h ) zero
   ∎
nat-nlist  h f (suc n)  = begin  -- to prove fmap f ( nlist h (suc n)  )  ≡ nlist ( f h ) (suc n )
        fmap f ( nlist h (suc n) )
   ≡⟨ refl ⟩
        (f h) :: fmap f ( nlist h n )
   ≡⟨ cong  (_::_ (f h)) (nat-nlist h f n) ⟩
        (f h) :: nlist ( f h ) n
   ∎



