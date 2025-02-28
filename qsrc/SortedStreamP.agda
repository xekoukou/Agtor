{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

module SortedStreamP where

 open import FunctorP
 open import Final-CoAlgebraP


 ℕ̂ : ℕ → 𝓤₀ ̇
 ℕ̂ zero = 𝟙
 ℕ̂ (succ n) = ℕ × ℕ̂  n

 Fℕ̂ : ℕ → Functor 𝓤₂
 Fℕ̂  n =
    (λ X → ℕ̂  n × X)
  , (λ f (k , x) → k , f x)
  , (λ f g x → refl)
  , λ x → refl

 Coℕ̂  : ℕ → 𝓤₂ ⁺ ̇
 Coℕ̂  n = Final-CoAlgebra (Fℕ̂  n)
