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

module Lists where

-- If we do not have two equal secrets in the same list, then this is a proposition
data _∈_ {A : 𝓤 ̇ } (x : A) : (ls : List A) → 𝓤  ̇  where
 here : ∀{y ls} → x ＝ y → x ∈ (y ∷ ls)
 there : ∀{y ls} → (ind : x ∈ ls) → x ∈ (y ∷ ls)

_⊃_ : {A : 𝓤 ̇ } (xs ys : List A) → 𝓤 ̇
xs ⊃ [] = 𝟙
xs ⊃ (y ∷ ys) = y ∈ xs × (xs ⊃ ys)

⊃-is-prop : {A : 𝓤 ̇ } → ∀ xs ys → ((x : A) → is-prop (x ∈ xs)) → is-prop (xs ⊃ ys)
⊃-is-prop xs [] _ = 𝟙-is-prop
⊃-is-prop xs (y ∷ ys) xs-is-prop = Σ-is-prop (xs-is-prop y) λ _ → ⊃-is-prop xs ys xs-is-prop

s⟨_⟩ : {A : 𝓤 ̇ } → (bs-secr scrs : List A) → 𝓤 ̇
s⟨ bs-secr ⟩ scrs = scrs ⊃ bs-secr × bs-secr ⊃ scrs


s⟨⟩-is-prop : {A : 𝓤 ̇ } → ∀ ascrs scrs → ((x : A) → is-prop (x ∈ ascrs)) → ((x : A) → is-prop (x ∈ scrs)) → is-prop (scrs ⊃ ascrs × ascrs ⊃ scrs)
s⟨⟩-is-prop ascrs scrs  d e = Σ-is-prop (⊃-is-prop _ _ e) (λ _ → ⊃-is-prop _ _ d)


