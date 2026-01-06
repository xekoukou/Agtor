
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

module Interleaving2 where

Fin : (n : ℕ) → 𝓤₀ ̇
Fin n = Σ x ꞉ ℕ , x ≤ n

last : ∀ {n} → (Fin n → ℕ) → 𝟚 → ℕ
last {n} f v = l1 n (≤-refl n) v where
 l1 : (x : ℕ) → (x ≤ n) → 𝟚 → ℕ
 l1 zero rl ₁ = succ (f (zero , rl))
 l1 zero rl ₀ = 0
 l1 (succ x) rl ₁ = succ (f (succ x , rl)) + l1 x (≤-trans x (succ x) n (≤-succ x) rl) ₀
 l1 (succ x) rl ₀ = l1 x (≤-trans x (succ x) n (≤-succ x) rl) ₁

BFun : (n : ℕ) → ℕ → ℕ → 𝓤₀ ̇
BFun n k l = Σ f ꞉ (Fin n → ℕ) , (last f ₀ ＝ k) × (last f ₁ ＝ l)



open import PredP
open ΣPred
open import FunctorP
open import CoAlgebraP
open import Final-CoAlgebraP
import PotP as P

module Interleave  (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  )  𝓥 𝓦 𝓠 (fc-pot : P.Pot Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠) where

 open import Definitions Msg Secret
 open ΣPred
 open P Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠
 open Functor Fpot
 open CoAlgebra Fpot
 open Final-CoAlgebra Fpot fc-pot
 open import FCP Msg Secret 𝓥 ⟨ fc ⟩
 open FC
 open Pot {fc-pot}
 open import StreamP

 PSet×PSet' = PSet×PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠
 module DD (sfc' : Stream PSet×PSet') where
  open Stream sfc' renaming (next to nextₛ)
  open Functor (FStream PSet×PSet') renaming (Fn to Fnₛ)
  open CoAlgebra (FStream PSet×PSet')renaming (⟨_⟩ to ⟨_⟩ₛ ; _⟶ to _⟶ₛ)
  open Final-CoAlgebra (FStream PSet×PSet') sfc' renaming (fc to fcₛ ; uni to uniₛ)
  
  d : (ℕ → ℕ) → Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩ × 𝟚 × ℕ × ℕ → Fnₛ (Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩ × 𝟚 × ℕ × ℕ)
  d f (a , b , ₀ , nf , zero) = (pset a , pset b) , (a , (fc ⟶) (next b) , ₁ , succ nf , f nf)
  d f (a , b , ₁ , nf , zero) = (pset a , pset b) , ((fc ⟶) (next a) , b , ₀ , succ nf , f nf)
  d f (a , b , ₀ , nf , succ rn) = (pset a , pset b) , (a , (fc ⟶) (next b) , ₀ , nf , rn)
  d f (a , b , ₁ , nf , succ rn) = (pset a , pset b) , ((fc ⟶) (next a) , b , ₁ , nf , rn)
  
  d-co : ∀ f → CoAlgebra (FStream PSet×PSet')
  d-co f =  (Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩ × 𝟚 × ℕ × ℕ) , d f

  interleave : ∀ f → 𝟚 → (a b : Fn ⟨ fc ⟩) → ⟨ fcₛ ⟩ₛ
  interleave f o a b = (uniₛ (d-co f) .pr₁ ↓) (a , b , o , 0 , f 0) where
   open CoAlgebra₂ (FStream _) (d-co f) fcₛ
   open Morphism












-- Increasing : (f : ℕ → ℕ) → 𝓤₀ ̇
-- Increasing f = ∀ x y → succ x ≤ y → succ (f x) ≤ f y

-- Starts-from-zero : (f : ℕ → ℕ) → 𝓤₀ ̇
-- Starts-from-zero f = f 0 ＝ 0

-- Zero-Increasing : (f : ℕ → ℕ) → 𝓤₀ ̇
-- Zero-Increasing f = Increasing f × Starts-from-zero f

-- Fin-Increasing : (n : ℕ) → (f : Fin n → ℕ) → 𝓤₀ ̇
-- Fin-Increasing n f = ∀ (x y : Fin n) → succ < x > ≤ < y > → succ (f x) ≤ f y


-- Starts-from-fzero : (n : ℕ) → (f : Fin n → ℕ) → 𝓤₀ ̇
-- Starts-from-fzero n f = f (0 , ⋆) ＝ 0

-- Zero-Fin-Increasing : (n : ℕ) → (f : Fin n → ℕ) → 𝓤₀ ̇
-- Zero-Fin-Increasing n f = Fin-Increasing n f × Starts-from-fzero n f

-- Interleaving : 𝓤₀ ̇
-- Interleaving = 𝟚 × Σ Zero-Increasing × Σ Zero-Increasing

-- Fin-Interleaving : 𝓤₀ ̇
-- Fin-Interleaving = Σ λ n → (Σ (Zero-Fin-Increasing n) × Σ (Zero-Fin-Increasing (succ n))) ＋ (Σ (Zero-Fin-Increasing (succ n)) × Σ (Zero-Fin-Increasing n))

-- -- In some cases we only care for the last value before
-- -- a communication happens between the two potentialities.
-- -- TODO ???
-- G : Fin-Interleaving → ℕ → ℕ → 𝓤₀ ̇
-- G (n , inl ((f , _) , g , _)) k l = (f (n , ≤-refl n) ＝ k) × (g (succ n , ≤-refl n) ＝ l)
-- G (n , inr ((f , _) , g , _)) k l = (f (succ n , ≤-refl n) ＝ k) × (g (n , ≤-refl n) ＝ l)


-- -- given a function f, we can get a function that is strictly increasing
-- inc : (ℕ → ℕ) → ℕ → ℕ
-- inc f zero = 0
-- inc f (succ x) = (inc f x) + succ (f x)

-- inc-Inc : (f : ℕ → ℕ) → Increasing (inc f)
-- inc-Inc f x y eq with subtraction (succ x) y eq
-- ... | k , ee with (addition-commutativity x (succ k)) ∙ succ-left k x ∙ ee
-- inc-Inc f x y eq | zero , ee | refl = ≤-+ (inc f x) (f x)
-- inc-Inc f x y eq | succ k , ee | refl = ≤-trans (inc f x) (inc f (x + k) + f (x + k)) (succ (inc f (x + k) + f (x + k)) + f (succ (x + k))) (inc-Inc f x (succ (x + k)) (≤-+ x k)) (≤-trans (inc f (x + k) + f (x + k)) (succ (inc f (x + k) + f (x + k))) (succ (inc f (x + k) + f (x + k)) + f (succ (x + k))) (≤-succ (inc f (x + k) + f (x + k))) (≤-+ (succ (inc f (x + k) + f (x + k))) (f (succ (x + k)))))

-- inc-Zero-Inc : (f : ℕ → ℕ) → Zero-Increasing (inc f)
-- inc-Zero-Inc f .pr₁ = inc-Inc f
-- inc-Zero-Inc f .pr₂ = refl

-- open import FunctorP
-- open import CoAlgebraP
-- open import Final-CoAlgebraP
-- import PotP as P

-- module Interleave  (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  )  𝓥 𝓦 𝓠 (fc-pot : P.Pot Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠) where

--  open import Definitions Msg Secret
--  open ΣPred
--  open P Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠
--  open Functor Fpot
--  open CoAlgebra Fpot
--  open Final-CoAlgebra Fpot fc-pot
--  open import FCP Msg Secret 𝓥 ⟨ fc ⟩
--  open FC
--  open Pot {fc-pot}
--  open import StreamP

--  PSet×PSet' = PSet×PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠
--  module DD (sfc' : Stream PSet×PSet') where
--   open Stream sfc' renaming (next to nextₛ)
--   open Functor (FStream PSet×PSet') renaming (Fn to Fnₛ)
--   open CoAlgebra (FStream PSet×PSet')renaming (⟨_⟩ to ⟨_⟩ₛ ; _⟶ to _⟶ₛ)
--   open Final-CoAlgebra (FStream PSet×PSet') sfc' renaming (fc to fcₛ ; uni to uniₛ)
  
--   d : (ℕ → ℕ) × (ℕ → ℕ) → Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩ × 𝟚 × ℕ × ℕ × ℕ → Fnₛ (Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩ × 𝟚 × ℕ × ℕ × ℕ)
--   d (f , g) (a , b , ₀ , nf , ng , zero) = (pset a , pset b) , (a , (fc ⟶) (next b) , ₁ , succ nf , ng , f nf)
--   d (f , g) (a , b , ₁ , nf , ng , zero) = (pset a , pset b) , ((fc ⟶) (next a) , b , ₀ , nf , succ ng , g ng)
--   d (f , g) (a , b , ₀ , nf , ng , succ rn) = (pset a , pset b) , (a , (fc ⟶) (next b) , ₀ , nf , ng , rn)
--   d (f , g) (a , b , ₁ , nf , ng , succ rn) = (pset a , pset b) , ((fc ⟶) (next a) , b , ₁ , nf , ng , rn)
  
--   d-co : ∀ f g → CoAlgebra (FStream PSet×PSet')
--   d-co f g =  (Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩ × 𝟚 × ℕ × ℕ × ℕ) , d (f , g)

--   interleave : ∀ f g → 𝟚 → ∀ k → (a b : Fn ⟨ fc ⟩) → ⟨ fcₛ ⟩ₛ
--   interleave f g o k a b = (uniₛ (d-co f g) .pr₁ ↓) (a , b , o , 0 , 0 , k) where
--    open CoAlgebra₂ (FStream _) (d-co f g) fcₛ
--    open Morphism


