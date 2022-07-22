{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.List

module Common where


data _∈_ {ℓ} {A : Type ℓ} (y : A) : List A → Type ℓ where
  more : ∀{x xs} → y ∈ xs → y ∈ (x ∷ xs)
  here : ∀ {xs} → y ∈ (y ∷ xs)

