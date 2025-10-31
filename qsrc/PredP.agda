{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

module PredP (A : 𝓤 ̇) where

Pred : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
Pred 𝓥 = (x : A) → 𝓥 ̇ 

module Pred₂ (a b : Pred 𝓥) where
 _&&_ : Pred 𝓥
 _&&_ x = a x × b x

 _||_ : Pred 𝓥
 _||_ x = a x + b x


-- Should the condition be on the same universe.
-- we mostly want propositions ???
PCon : ∀ q → _
PCon q = Pred q → 𝓤 ⊔ q ̇

ΣPred : ∀ 𝓥 → PCon 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
ΣPred 𝓥 C = Σ C

module ΣPred {C} (P : ΣPred 𝓥 C) where

 type : (A → 𝓥 ̇)
 type = P .pr₁

 prop : C type
 prop = P .pr₂
