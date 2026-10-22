
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Interleaving
/*
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split --guardedness #-}

open import MLTT.Spartan renaming (_+_ to _＋_)
open import Naturals.Addition
open import UF.FunExt
open import UF.PropTrunc
open import Naturals.Order
open import Notation.Order
open import Naturals.Properties
open import MLTT.Two-Properties


```
*/

```agda

module Interleaving where

open import PredP
open ΣPred


Increasing : (f : ℕ → ℕ) → 𝓤₀ ̇
Increasing f = ∀ x y → succ x ≤ y → succ (f x) ≤ f y

Starts-from-zero : (f : ℕ → ℕ) → 𝓤₀ ̇
Starts-from-zero f = f 0 ＝ 0

Zero-Increasing : (f : ℕ → ℕ) → 𝓤₀ ̇
Zero-Increasing f = Increasing f × Starts-from-zero f

Fin : (n : ℕ) → 𝓤₀ ̇
Fin n = Σ x ꞉ ℕ , x ≤ n

Fin-Increasing : (n : ℕ) → (f : Fin n → ℕ) → 𝓤₀ ̇
Fin-Increasing n f = ∀ (x y : Fin n) → succ < x > ≤ < y > → succ (f x) ≤ f y


Starts-from-fzero : (n : ℕ) → (f : Fin n → ℕ) → 𝓤₀ ̇
Starts-from-fzero n f = f (0 , ⋆) ＝ 0

Zero-Fin-Increasing : (n : ℕ) → (f : Fin n → ℕ) → 𝓤₀ ̇
Zero-Fin-Increasing n f = Fin-Increasing n f × Starts-from-fzero n f

Interleaving : 𝓤₀ ̇
Interleaving = 𝟚 × Σ Zero-Increasing × Σ Zero-Increasing

Fin-Interleaving : 𝓤₀ ̇
Fin-Interleaving = Σ λ n → (Σ (Zero-Fin-Increasing n) × Σ (Zero-Fin-Increasing (succ n))) ＋ (Σ (Zero-Fin-Increasing (succ n)) × Σ (Zero-Fin-Increasing n))

-- In some cases we only care for the last value before
-- a communication happens between the two potentialities.
-- TODO ???
G : Fin-Interleaving → ℕ → ℕ → 𝓤₀ ̇
G (n , inl ((f , _) , g , _)) k l = (f (n , ≤-refl n) ＝ k) × (g (succ n , ≤-refl n) ＝ l)
G (n , inr ((f , _) , g , _)) k l = (f (succ n , ≤-refl n) ＝ k) × (g (n , ≤-refl n) ＝ l)


-- given a function f, we can get a function that is strictly increasing
inc : (ℕ → ℕ) → ℕ → ℕ
inc f zero = 0
inc f (succ x) = (inc f x) + succ (f x)

inc-Inc : (f : ℕ → ℕ) → Increasing (inc f)
inc-Inc f x y eq with subtraction (succ x) y eq
... | k , ee with (addition-commutativity x (succ k)) ∙ succ-left k x ∙ ee
inc-Inc f x y eq | zero , ee | refl = ≤-+ (inc f x) (f x)
inc-Inc f x y eq | succ k , ee | refl = ≤-trans (inc f x) (inc f (x + k) + f (x + k)) (succ (inc f (x + k) + f (x + k)) + f (succ (x + k))) (inc-Inc f x (succ (x + k)) (≤-+ x k)) (≤-trans (inc f (x + k) + f (x + k)) (succ (inc f (x + k) + f (x + k))) (succ (inc f (x + k) + f (x + k)) + f (succ (x + k))) (≤-succ (inc f (x + k) + f (x + k))) (≤-+ (succ (inc f (x + k) + f (x + k))) (f (succ (x + k)))))

inc-Zero-Inc : (f : ℕ → ℕ) → Zero-Increasing (inc f)
inc-Zero-Inc f .pr₁ = inc-Inc f
inc-Zero-Inc f .pr₂ = refl
