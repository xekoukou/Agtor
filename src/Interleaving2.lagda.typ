
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

-- last : ∀ {n} → (Fin n → ℕ) → 𝟚 → ℕ
-- last {n} f v = l1 n (≤-refl n) v where
--  l1 : (x : ℕ) → (x ≤ n) → 𝟚 → ℕ
--  l1 zero rl ₁ = succ (f (zero , rl))
--  l1 zero rl ₀ = 0
--  l1 (succ x) rl ₁ = succ (f (succ x , rl)) + l1 x (≤-trans x (succ x) n (≤-succ x) rl) ₀
--  l1 (succ x) rl ₀ = l1 x (≤-trans x (succ x) n (≤-succ x) rl) ₁

-- index , index + 1 total elements
index : ∀{n} → (Fin n → ℕ) → ℕ
index {zero} f = f (0 , ⋆)
index {succ n} f = (index {n = n} λ (r , rl) → f ((succ r) , rl)) + succ (f (0 , ⋆))

-- ₁ is left , ₀ is right
succ× : 𝟚 × ℕ × ℕ → ℕ × ℕ
succ× (₀ , a , b) = a , succ b
succ× (₁ , a , b) = succ a , b

n-succ× : (n : ℕ) → 𝟚 → ℕ × ℕ → (Fin n → ℕ × ℕ)
n-succ× n two q (zero , rl) = succ× (two , q)
n-succ× (succ n) two q (succ r , rl) = n-succ× n two (succ× (two , q)) (r , rl)

_+ᶠ_ : ∀{𝓦} → {A : 𝓦 ̇ } → ∀{n k} → (Fin n → A) → (Fin k → A) → Fin (n + (succ k)) → A
_+ᶠ_ {A = A} {n} {k} f1 f2 (zero , rl) = f2 (0 , ⋆)
_+ᶠ_ {A = A} {n} {zero} f1 f2 (succ r , rl) = f1 (r , rl)
_+ᶠ_ {A = A} {n} {succ k} f1 f2 (succ r , rl) = _+ᶠ_ {n = n} {k = k} f1 (λ (r , rl) → f2 (succ r , rl)) (r , rl)

-- TODO Can we simplify this?
enum'-fin : ∀{n} → (f : Fin n → ℕ) → 𝟚 → ℕ × ℕ → Fin (index f) → ℕ × ℕ
enum'-fin {zero} f two q = n-succ× (f (0 , ⋆)) two q
enum'-fin {succ n} f two q
 = let r2 = n-succ× (f (0 , _)) two q
       r1 = enum'-fin (λ (r , rl) → f (succ r , rl)) (complement two) (r2 (f (0 , _) , ≤-refl (f (0 , _))))
   in r1 +ᶠ r2

enum-fin : ∀{n} → (f : Fin n → ℕ) → 𝟚 → Fin (index f) → ℕ × ℕ
enum-fin f two = enum'-fin f two (0 , 0)


BFun : (n : ℕ) → ℕ → ℕ → 𝓤₀ ̇
BFun n l r = Σ f ꞉ (Fin n → ℕ) , Σ two ꞉ 𝟚 , let last = enum-fin f two (index f , ≤-refl (index f)) in (last .pr₁ ＝ l) × (last .pr₂ ＝ r)


_+ⁱᶠ_ : ∀{𝓦} → {A : 𝓦 ̇ } → ∀{k} → (ℕ → A) → (Fin k → A) → ℕ → A
_+ⁱᶠ_ {A = A} {k} f1 f2 zero = f2 (0 , ⋆)
_+ⁱᶠ_ {A = A} {zero} f1 f2 (succ r) = f1 r
_+ⁱᶠ_ {A = A} {succ k} f1 f2 (succ r) = _+ⁱᶠ_ {k = k} f1 (λ (r , rl) → f2 (succ r , rl)) r


ind-succ× : (f : ℕ → ℕ) → ((𝟚 × ℕ × ℕ) × ℕ × ℕ) → (𝟚 × ℕ × ℕ) × ℕ × ℕ
ind-succ× f ((two , nf , zero) , r) = (complement two , succ nf , f nf) , succ× (two , r)
ind-succ× f ((two , nf , succ q) , r) = (two , nf , q) , succ× (two , r)

enum'-inf : (f : ℕ → ℕ) → (𝟚 × ℕ × ℕ) × ℕ × ℕ → ℕ → (𝟚 × ℕ × ℕ) × ℕ × ℕ
enum'-inf f e zero = ind-succ× f e
enum'-inf f e (succ r) = let w = ind-succ× f e in enum'-inf f w r 

enum-inf : (f : ℕ → ℕ) → 𝟚 → ℕ → ℕ × ℕ
enum-inf f two r = enum'-inf f ((two , 0 , f 0 ) , 0 , 0) r .pr₂


_∈ₚ_ : (ℕ × ℕ) → ∀{n l r} → BFun n l r → 𝓤₀ ̇
x ∈ₚ (f , two , lc , rc) = Σ i ꞉ Fin (index f) , enum-fin f two i ＝ x

_∈ₚᵢ_ : (ℕ × ℕ) → (ℕ →  ℕ) × 𝟚 → 𝓤₀ ̇
x ∈ₚᵢ (f , two) = Σ i ꞉ ℕ , enum-inf f two i ＝ x

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
 open import FCP Msg Secret 𝓥
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

  interleave : (ℕ → ℕ) × 𝟚 → (a b : Fn ⟨ fc ⟩) → ⟨ fcₛ ⟩ₛ
  interleave (f , o) a b = (uniₛ (d-co f) .pr₁ ↓) (a , b , o , 0 , f 0) where
   open CoAlgebra₂ (FStream _) (d-co f) fcₛ
   open Morphism
