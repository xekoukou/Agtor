{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc

module BSet2 (Msg : 𝓤 ̇) where

BSet : 𝓤 ⁺ ̇
BSet = (mp : Msg) → 𝓤 ̇ 


-- The property holds for all messages.
⊨ : BSet → 𝓤 ̇
⊨ P = ∀ a → P a  

⊥B : BSet
⊥B mp = 𝟘

⊤B : BSet
⊤B mp = 𝟙

_⟶_ : BSet → BSet → BSet
(P ⟶ Q) mp = P mp → Q mp

_&&_ : BSet → BSet → BSet
(a && b) mp = a mp × b  mp

_≡ᵇ_ : BSet → BSet → 𝓤 ̇
A ≡ᵇ B = ⊨ ((A ⟶ B) && (B ⟶ A))

¬ᵇ : BSet → BSet
(¬ᵇ A) mp = ¬ (A mp)

_─_ : BSet → BSet → BSet
(a ─ b) = a && (¬ᵇ b)

_||_ : BSet → BSet → BSet
(a || b) mp = a mp + b mp 
