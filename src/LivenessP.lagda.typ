
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Liveness
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

module LivenessP (fe : Fun-Ext) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) 𝓥 𝓦 𝓠 where

open import Interleaving2

open import PredP
open ΣPred

open import FunctorP
open import CoAlgebraP
open import Final-CoAlgebraP
import PotP as P

open import Definitions Msg Secret

module Liveness (fc-pot : P.Pot Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠) (R : <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠 → <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠 → 𝓣 ̇  ) where
 open P Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠
 open Functor Fpot
 open CoAlgebra Fpot
 open Final-CoAlgebra Fpot fc-pot
 open Pot {fc-pot}
 open Pot₁ fe {fc-pot}

 liveness-fiber : (d b : Fn ⟨ fc ⟩) → (ℕ → ℕ) × 𝟚 → 𝓣 ̇
 liveness-fiber d b f =
  let g = 2ℕ-inf f
   in (k : ℕ) → Σ n ꞉ ℕ , k ≤ n × let nd , nb = g n in R < pset (d at nd) > < pset (b at nb) >

 Interleaved-Condition : ∀ 𝓣  → 𝓣 ⁺ ̇
 Interleaved-Condition 𝓣 = (ℕ → ℕ) × 𝟚 → 𝓣 ̇

 Cond-Liveness : (a b : Fn ⟨ fc ⟩) → 𝓣 ⊔ 𝓦 ⁺ ̇  
 Cond-Liveness a b = Σ IC ꞉ Interleaved-Condition 𝓦 , ∀ r → IC r → liveness-fiber a b r

 Liveness : (a b : Fn ⟨ fc ⟩) → 𝓣 ̇
 Liveness a b = ∀ r → liveness-fiber a b r

 f2ℕ-ext' : ∀ left right → (ℕ → ℕ) × 𝟚 → (ℕ → ℕ)
 f2ℕ-ext' left right (f , ₀) zero = right
 f2ℕ-ext' left right (f , ₁) zero = left
 f2ℕ-ext' left right (f , ₀) (succ zero) = left
 f2ℕ-ext' left right (f , ₁) (succ zero) = right
 f2ℕ-ext' left right (f , two) (succ (succ x)) = f x

 f2ℕ-ext : ∀ left right → (ℕ → ℕ) × 𝟚 → (ℕ → ℕ) × 𝟚
 f2ℕ-ext left right f@(_ , two) = f2ℕ-ext' left right f , two

 f2ℕ-red : (ℕ → ℕ) × 𝟚 → ∀ t → (ℕ → ℕ) × 𝟚
 f2ℕ-red f2@(f , _) t = let ((two , nf , rem) , _) = 2ℕ-inf-s f2 t
                        in (λ { zero → rem ; (succ x) → f (nf + succ x)}) , two

 gg : ∀{a b} → (f g : (ℕ → ℕ) × 𝟚) → (Σ k ꞉ ℕ , Σ l ꞉ ℕ , ∀ n → 2ℕ-inf f (n + l) ＝ 2ℕ-inf g (n + k))
  → liveness-fiber a b f → liveness-fiber a b g
 gg {a} {b} f g (k , l , c) lv m
   = let (q , rl , lc) = lv (m + l)
         (e , erl') = subtraction (m + l) q rl
         erl = addition-associativity e m l ∙ erl' 
     in e + m + k , transport (λ z → z) (ap (λ z → m ≤ℕ z) (addition-associativity m e k ⁻¹ ∙ (ap (λ z → z + k) (addition-commutativity m e)))) (≤-+ m (e + k)) , transport (λ z → R < pset (a at z .pr₁) > < pset (b at z .pr₂) >) (ap (2ℕ-inf f) erl ⁻¹ ∙ c (e + m)) lc

 gg1' :  ∀{a b} → (f : (ℕ → ℕ) × 𝟚) → liveness-fiber a b f
         →  ∀ t → let (l , r) = 2ℕ-inf f t
                  in ∀ k → 2ℕ-inf (f2ℕ-red f t) k ＝ 2ℕ-inf f (t + k)
 gg1' f2@(f , tw) lv t k = {!!} where
  e = 2ℕ-inf-s f2 t
  two = e .pr₁ .pr₁
  nf = e .pr₁ .pr₂ .pr₁
  rem = e .pr₁ .pr₂ .pr₂
  l = e .pr₂ .pr₁
  r = e .pr₂ .pr₂
  l2 : (n : ℕ) →
      f (succ (nf + n)) ＝
      f2ℕ-red (f , tw) t .pr₁ (succ (0 + n))
  l2 n = transport (λ z → f (succ (nf + n)) ＝
      f2ℕ-red (f , tw) t .pr₁ (succ z)) (zero-left-neutral n ⁻¹) refl
  l1 = 2ℕ-inf'-l+n=k+n f (f2ℕ-red (f , tw) t .pr₁)
        (nf , 0 , l2) 0 two rem (l , r) k
  l3 = {!l1!}

 gg1 : ∀{a b} → (f : (ℕ → ℕ) × 𝟚) → ∀ l r
       → liveness-fiber (a at l) (b at r) f → liveness-fiber a b (f2ℕ-ext l r f)
 gg1 f l r lv k = {!!}
