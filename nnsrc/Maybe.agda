{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Plus
open import UF.FunExt
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Base

module Maybe where

𝟙+_ : ∀{𝓤} (X : 𝓤 ̇ ) → 𝓤 ̇
𝟙+_ {𝓤} X = 𝟙 {𝓤} + X

R₊ :  ∀{𝓤 𝓥} {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → (𝟙+ X) → (𝟙+ Y)
R₊ f (inl x) = inl _
R₊ f (inr x) = inr (f x)

R₊-comp : ∀{𝓤} {X Y Z : 𝓤 ̇} → (f : X → Y) → (g : Z → X) → ∀ x → (R₊ f) (R₊ g x) ＝ R₊ (f ∘ g) x
R₊-comp f g (inl x) = refl
R₊-comp f g (inr x) = refl

R₊-id : ∀{𝓤} {X : 𝓤 ̇} → R₊ id ∼ id {X = 𝟙+ X}
R₊-id (inl _) = refl
R₊-id (inr _) = refl

_<p_>_ : ∀{𝓤} {X : 𝓤 ̇} → (𝟙+ X) → (f : X → X → X) → X → X
inl x <p f > b = b
inr x <p f > b = f x b
