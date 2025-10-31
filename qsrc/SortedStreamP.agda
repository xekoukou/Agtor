{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import Naturals.Order
open import UF.Base

module SortedStreamP where

open import FunctorP
open import Final-CoAlgebraP
open import CoAlgebraP


ℕ̂ : ℕ → 𝓤₀ ̇
ℕ̂ zero = 𝟙
ℕ̂ (succ n) = ℕ × ℕ̂  n

_prₙ : ∀{n} → ℕ̂  n → ∀ l → succ l ≤ℕ n → ℕ
_prₙ {succ n} x zero rl = x .pr₁
_prₙ {succ n} x (succ l) rl = (x .pr₂ prₙ) l rl

Fℕ̂ : ℕ → Functor 𝓤₂
Fℕ̂  n =
   (λ X → ℕ̂  n × X)
 , (λ f (k , x) → k , f x)
 , (λ f g x → refl)
 , λ x → refl

Coℕ̂  : ℕ → 𝓤₂ ⁺ ̇
Coℕ̂  n = Final-CoAlgebra (Fℕ̂  n)

module CoFℕ̂  n (coFℕ̂  : CoAlgebra (Fℕ̂  n)) where

 open CoAlgebra (Fℕ̂  n) coFℕ̂ 

 _at_ : type → ℕ → type
 _at_ x zero = x 
 _at_ x (succ n) = (morph x .pr₂) at n
 
 Ordered : type → 𝓤₀ ̇
 Ordered x = ∀ k l → (rl : succ l ≤ℕ n) → ((morph (x at k) .pr₁) prₙ) l rl ≤ℕ ((morph (x at (succ k)) .pr₁) prₙ) l rl


module Coℕ̂  n (coFℕ̂  : CoAlgebra (Fℕ̂  n)) (coℕ̂  : Coℕ̂  n) where
 
 open CoFℕ̂  n coFℕ̂
 open CoAlgebra (Fℕ̂  n) coFℕ̂ 
 private
  module F = Final-CoAlgebra (Fℕ̂  n) coℕ̂
  module Fp = CoFℕ̂  n (coℕ̂  .pr₁)

 open CoAlgebra₂ (Fℕ̂  n) coFℕ̂  F.fc
 private
  module UMorph = Morphism (F.uni coFℕ̂  .pr₁)


 g : (x : type) → Ordered x → Fp.Ordered (UMorph.morphism x)
 g x ord k l rl
  = transport₂ (λ z a → z l rl ≤ℕ a l rl)
     (ap (λ z → z .pr₁ prₙ) (UMorph.property (x at k)) ∙ ap (λ z → F.morph z .pr₁ prₙ) (l1 x k ⁻¹))
     ((ap (λ z → z .pr₁ prₙ) (UMorph.property (x at (succ k))) ∙ ap (λ z → F.morph z .pr₁ prₙ) (l1 x (succ k) ⁻¹))) (ord k l rl) where
  l1 : ∀ x k → UMorph.morphism x Fp.at k ＝ UMorph.morphism (x at k)
  l1 x zero = refl
  l1 x (succ k) = ap (λ z → (z .pr₂) Fp.at k) ((UMorph.property x) ⁻¹) ∙ l1 (morph x .pr₂) k
