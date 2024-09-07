{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (𝟚)
open import MLTT.Negation
open import MLTT.Empty
open import MLTT.Plus
open import UF.FunExt
open import UF.Univalence
open import UF.Equiv
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Base

module Secret (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇ ) (s-is-set : is-set Secret) (decS : is-decidable Secret) where

open PropositionalTruncation pt
open import BSet {𝓤} fe pt

S×Msg : 𝓤 ̇
S×Msg = List Secret × (Secret + Msg)

open import PSet fe pt S×Msg

data _∈_ (x : Secret) : (ls : List Secret) → 𝓤  ̇  where
 here : ∀{y ls} → x ＝ y → x ∈ (y ∷ ls)
 there : ∀{y ls} → ¬ (y ＝ x) → (ind : x ∈ ls) → x ∈ (y ∷ ls)

∈-is-prop : ∀ x ls → is-prop (x ∈ ls)
∈-is-prop x .(_ ∷ _) (here eq) (here eq2) = ap here (s-is-set eq eq2)
∈-is-prop x .(_ ∷ _) (here eq) (there neq y) = 𝟘-elim (neq (eq ⁻¹))
∈-is-prop x .(_ ∷ _) (there neq z) (here eq) = 𝟘-elim (neq (eq ⁻¹))
∈-is-prop x (_ ∷ ls) (there neq z) (there neq2 y)
 = ap (λ (x , y) → there x y)
    (to-Σ-＝
      (dfunext fe (λ z → 𝟘-elim (neq z))
     , ∈-is-prop x ls (transport (λ _ → x ∈ ls) (dfunext fe (λ z₁ → 𝟘-elim (neq z₁))) z) y))

_⊃_ : (xs ys : List Secret) → 𝓤 ̇
xs ⊃ [] = 𝟙
xs ⊃ (y ∷ ys) = y ∈ xs × (xs ⊃ ys)

⊃-is-prop : ∀ xs ys → is-prop (xs ⊃ ys)
⊃-is-prop xs [] = 𝟙-is-prop
⊃-is-prop xs (y ∷ ys) = Σ-is-prop (∈-is-prop _ _) (λ _ → ⊃-is-prop xs ys)


S×BSet : List Secret → BSet Msg → BSet S×Msg
⟨ S×BSet pscrs bs ⟩ (scrs , inr msg) = scrs ⊃ pscrs × pscrs ⊃ scrs × ⟨ bs ⟩  msg
⟨ S×BSet pscrs bs ⟩ (scrs , inl _) = 𝟘
-is-prop (S×BSet pscrs bs) (scrs , inr msg) = Σ-is-prop (⊃-is-prop _ _) λ _ → Σ-is-prop (⊃-is-prop _ _) λ _ → bs .-is-prop msg

isSecret : List Secret → BSet S×Msg
⟨ isSecret pscrs ⟩ (scrs , inl x) = scrs ⊃ pscrs × pscrs ⊃ scrs
⟨ isSecret pscrs ⟩ (scrs , inr x) = 𝟘
-is-prop (isSecret pscrs) (scrs , inl x) = Σ-is-prop (⊃-is-prop _ _) λ _ → ⊃-is-prop _ _
-is-prop (isSecret pscrs) (scrs , inr x) = 𝟘-is-prop

hasSecret : List Secret → Secret → BSet S×Msg
⟨ hasSecret pscrs scr ⟩ (scrs , inl x) = scrs ⊃ pscrs × pscrs ⊃ scrs × (x ＝ scr)
⟨ hasSecret pscrs scr ⟩ (scrs , inr x) = 𝟘
-is-prop (hasSecret pscrs scr) (scrs , inl x) = Σ-is-prop (⊃-is-prop _ _) λ _ → Σ-is-prop (⊃-is-prop _ _) λ _ → s-is-set
-is-prop (hasSecret pscrs scr) (scrs , inr x) = 𝟘-is-prop
