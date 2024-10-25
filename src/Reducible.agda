{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Negation
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

open import Lists

module Reducible (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) (dec : (a b : Secret) → is-decidable (a ＝ b))  where

open list-decidable dec

open PropositionalTruncation pt
open import UF.ImageAndSurjection pt

open import xBSet fe pt Msg Secret



module _ {𝓥} {𝓦} {𝓣} where
 
 b𝓤 = 𝓤 ⊔ 𝓥
 &𝓤 = 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦
 p𝓤 = 𝓤 ⁺⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣
 
 open import &PSet (𝟚 × ×BSet b𝓤) pt
 import PSet as P
 open P pt (&PSet &𝓤 × &PSet &𝓤)
 module E &𝓤 = P pt (&PSet &𝓤)
 open E renaming (PSet to ESet)



-- open import CoAlgebra fe pt UA Msg Secret {b𝓤} {&𝓤} {p𝓤}
 
 
 Σbs : &PSet 𝓦' → b𝓤 ⁺ ⊔ 𝓦' ̇
 Σbs &p = Σ bs ꞉ ×BSet b𝓤 , &⟨ &p ⟩ (₁ , bs)
 
 -- Here we assume a finite coverring
 msg-reducible : ×BSet b𝓤 → &PSet 𝓦' → b𝓤 ⁺ ⊔ 𝓦' ̇
 msg-reducible mbs &p
  =   Σ ls ꞉ List (Σbs &p)
    , (∀ x → ⟨ mbs bset ⟩ x → Σ l ꞉ Σbs &p , Σ o ꞉ l ∈ ls , ⟨ l .pr₁ bset ⟩ x)

-- The general case
 msg-reducible-g : ×BSet b𝓤 → &PSet 𝓦' → b𝓤 ⁺ ⊔ 𝓦' ̇
 msg-reducible-g mbs &p
  = (∀ x → ⟨ mbs bset ⟩ x → Σ l ꞉ Σbs &p , ⟨ l .pr₁ bset ⟩ x)
 
 &PSet-reducible→ : &PSet 𝓦' → &PSet 𝓣' → b𝓤 ⁺ ⊔ 𝓦' ⊔ 𝓣' ̇
 &PSet-reducible→ a b = Σ bs ꞉ ×BSet b𝓤 , Σ i ꞉ &⟨ a ⟩ (₀ , bs) , msg-reducible bs b
 
 &PSet-reducible : &PSet 𝓦' → &PSet 𝓣' → b𝓤 ⁺ ⊔ 𝓦' ⊔ 𝓣' ̇
 &PSet-reducible a b = &PSet-reducible→ a b + &PSet-reducible→ b a
 
 ESet-reducible-fiber : &PSet 𝓤' → ESet 𝓦' 𝓣' → b𝓤 ⁺ ⊔ 𝓤' ⊔ 𝓦' ⁺ ⊔ 𝓣' ̇
 ESet-reducible-fiber &pa pb = ∀ &pb → ∣⟨ pb ⟩ &pb → &PSet-reducible &pa &pb

 -- Here we ingore the internal reduction alltogether.
 -- ESet reduction means that we can prove that in all cases, it can
 -- reduce enxternally
 ESet-reducible : ESet 𝓦' 𝓣' → ESet 𝓤' 𝓥' → b𝓤 ⁺ ⊔ 𝓦' ⁺ ⊔ 𝓣' ⊔ 𝓤' ⁺ ⊔ 𝓥' ̇
 ESet-reducible pa pb = ∀ &pa → ∣⟨ pa ⟩ &pa → ESet-reducible-fiber &pa pb

 -- Here we ingore the external reduction alltogether.
 -- ESet reduction means that we can prove that in all cases, it can
 -- reduce internally
 
 -- Since we are talking about the same system,
 -- a system can only exist in one superposition.
 Self-reducible : ESet 𝓦' 𝓣' → b𝓤 ⁺ ⊔ (𝓦' ⁺) ⊔ 𝓣' ̇
 Self-reducible pa = ∀ &pa → ∣⟨ pa ⟩ &pa → &PSet-reducible &pa &pa


 PSet-ctx-reducible-fiber : &PSet &𝓤 × &PSet &𝓤 → ESet 𝓦' 𝓣' → &𝓤 ⊔ (𝓦' ⁺) ⊔ 𝓣' ̇
 PSet-ctx-reducible-fiber (&pa , &ic) ctx = ESet-reducible-fiber &pa ctx + &PSet-reducible &ic &ic 

 PSet-ctx-reducible : PSet p𝓤 → ESet 𝓦' 𝓣' → p𝓤 ⊔ (𝓦' ⁺) ⊔ 𝓣' ̇
 PSet-ctx-reducible pa ctx = ∀ &pa &ic → ∣⟨ pa ⟩ (&pa , &ic) → PSet-ctx-reducible-fiber (&pa , &ic) ctx

 _toCtx : PSet p𝓤 → ESet &𝓤 p𝓤
 ∣⟨ pa toCtx ⟩ o = ∃ λ &ps → ∣⟨ pa ⟩ (o , &ps)
 (pa toCtx) .∣-is-prop = λ o → ∥∥-is-prop

 _toInt : PSet p𝓤 → ESet &𝓤 p𝓤
 ∣⟨ pa toInt ⟩ o = ∃ λ &ps → ∣⟨ pa ⟩ (&ps , o)
 (pa toInt) .∣-is-prop = λ o → ∥∥-is-prop


 PSet-PSet-reducible-fiber : &PSet &𝓤 × &PSet &𝓤 → &PSet &𝓤 × &PSet &𝓤 → &𝓤 ̇
 PSet-PSet-reducible-fiber &a@(&pa , &ica) &b@(&pb , &icb) = &PSet-reducible &pa &pb + &PSet-reducible &ica &ica + &PSet-reducible &icb &icb

 PSet-PSet-reducible : PSet p𝓤 → PSet p𝓤 → p𝓤 ̇
 PSet-PSet-reducible pa pb = ∀ &pa &ica → ∣⟨ pa ⟩ (&pa , &ica) → ∀ &pb &icb → ∣⟨ pb ⟩ (&pb , &icb) → PSet-PSet-reducible-fiber (&pa , &ica) (&pb , &icb)


 _⊑_ : PSet p𝓤 → PSet p𝓤 → 𝓤ω 
 pa ⊑ pb = ∀{𝓦' 𝓣'} → (ctx : ESet 𝓦' 𝓣') → PSet-ctx-reducible pb ctx → PSet-ctx-reducible pa ctx 

 Fun : ESet &𝓤 p𝓤 → p𝓤 ̇
 Fun p = (q : Σ t ꞉ &PSet &𝓤 , ∣⟨ p ⟩ t) → Σ bs ꞉ 𝟚 × ×BSet b𝓤 , &⟨ q .pr₁ ⟩ bs

 F⇒&P : ∀{p} → Fun p → &PSet p𝓤
 &⟨ F⇒&P f ⟩ = _∈image λ x → f x .pr₁
 (F⇒&P f) .&-is-prop = λ o → ∥∥-is-prop
 
 _ᵀ : ESet &𝓤 p𝓤 → ESet p𝓤 (p𝓤 ⁺)
 ∣⟨ p ᵀ ⟩ = _∈image F⇒&P {p = p}
 (p ᵀ) .∣-is-prop = λ o → ∥∥-is-prop


 Fun' : PSet p𝓤 → p𝓤 ̇
 Fun' p = (q : Σ t ꞉ &PSet &𝓤 × &PSet &𝓤 , ∣⟨ p ⟩ t × (¬ &PSet-reducible (t .pr₂) (t .pr₂))) → Σ bs ꞉ 𝟚 × ×BSet b𝓤 , &⟨ q .pr₁ .pr₁ ⟩ bs

 F⇒&P' : ∀{p} → Fun' p → &PSet p𝓤
 &⟨ F⇒&P' f ⟩ = _∈image λ x → f x .pr₁
 (F⇒&P' f) .&-is-prop = λ o → ∥∥-is-prop
 
 _ᵀ' : PSet p𝓤 → ESet p𝓤 (p𝓤 ⁺)
 ∣⟨ p ᵀ' ⟩ = _∈image F⇒&P' {p = p}
 (p ᵀ') .∣-is-prop = λ o → ∥∥-is-prop

 theorem : (a b : PSet p𝓤) → PSet-ctx-reducible a (b ᵀ') → a ⊑ b
 theorem a b abt-red ctx ac-red &bp &bi pi∈b = {!!}
