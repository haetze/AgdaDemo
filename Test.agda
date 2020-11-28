module Test where

--import Agda.Builtin.TrustMe

data B : Set where
  true false : B


not : B -> B
not true = false
not false = true


_and_ : B -> B -> B
true and true = true
true and false = false
false and true = false
false and false = false


data N : Set where
  Z : N
  S : N -> N


_plus_ : N -> N -> N
Z plus b = b
S a plus b = S (a plus b)


infix 4 _eq_
data _eq_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x eq x
{-# BUILTIN EQUALITY _eq_  #-}
{-# BUILTIN REFL     refl #-}

prf1 : (a : N) -> (b : N) -> (a plus S b) eq (S (a plus b))
prf1 Z b = refl
prf1 (S a) b rewrite prf1 a b = refl

prf2 : (b : B) -> b and false eq false
prf2 true = refl
prf2 false = refl


