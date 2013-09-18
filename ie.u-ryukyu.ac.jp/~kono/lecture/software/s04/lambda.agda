module lambda where

postulate A : Set
postulate B : Set
postulate f : A -> B
postulate a : A

b : B
b = f a

g : A -> A
g = \x -> x

h : A -> A
h a = a

postulate P : (A -> A) -> Set

k : P g -> P h
k x = x

A2 : Set
A2 = A -> A
-- A2 = A -> B

A3 : Set
A3 = A2 -> A2

a2 : A2
a2 = \x -> x



