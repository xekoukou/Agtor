{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

module Test where

data A : Set where
  O : A
  b : A


B : A → Set
B O = Bool
B b = ℕ

postulate
  g : (x : A) → B x

f : A → Bool ⊎ ℕ
f x with g x
f O | r = inl r
f b | r = inr r

l1 : {A B : Set} → Dec A → {!!}
l1 = {!!}
