
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Operators
/*
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split #-}


open import MLTT.Spartan renaming (_+_ to _or_)
open import Naturals.Addition
open import UF.FunExt
open import UF.PropTrunc
open import Naturals.Order
open import Notation.Order
open import Naturals.Properties


```
*/

```agda
open import FunctorP
open import CoAlgebraP
open import Final-CoAlgebraP
open import PredP
open Pred

module Operators (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  )  𝓥 𝓦 𝓠 where

open import Definitions Msg Secret

open ΣPred
open import PotP Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠


data IV : 𝟚 → 𝓤₀ ̇ where
 _[_,_] : ℕ → ℕ → ℕ → IV ₀
 [_,_]_ : ℕ → ℕ → ℕ → IV ₁

module _ (pot : Pot) where

 open Functor Fpot
 open CoAlgebra Fpot
 open Final-CoAlgebra Fpot pot

 open import FCP Msg Secret 𝓥 ⟨ fc ⟩ 
 open FC

 PotSet : ∀ 𝓣 → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺ ⊔ 𝓣 ⁺ ̇
 PotSet 𝓣 = Fn ⟨ fc ⟩ → 𝓣 ̇

 PotSet₂ : ∀ 𝓣 → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺ ⊔ 𝓣 ⁺ ̇
 PotSet₂ 𝓣 = Fn ⟨ fc ⟩ → Fn ⟨ fc ⟩ → 𝓣 ̇


 Increasing : (f : ℕ → ℕ) → 𝓤₀ ̇
 Increasing f = ∀ x y → succ x ≤ y → succ (f x) ≤ f y

-- given a function f, we can get a function that is strictly increasing
 inc : (ℕ → ℕ) → ℕ → ℕ
 inc f zero = 0
 inc f (succ x) = (inc f x) + succ (f x)

 inc-Inc : (f : ℕ → ℕ) → Increasing (inc f)
 inc-Inc f x y eq with subtraction (succ x) y eq
 ... | k , ee with (addition-commutativity x (succ k)) ∙ succ-left k x ∙ ee
 inc-Inc f x y eq | zero , ee | refl = ≤-+ (inc f x) (f x)
 inc-Inc f x y eq | succ k , ee | refl = ≤-trans (inc f x) (inc f (x + k) + f (x + k)) (succ (inc f (x + k) + f (x + k)) + f (succ (x + k))) (inc-Inc f x (succ (x + k)) (≤-+ x k)) (≤-trans (inc f (x + k) + f (x + k)) (succ (inc f (x + k) + f (x + k))) (succ (inc f (x + k) + f (x + k)) + f (succ (x + k))) (≤-succ (inc f (x + k) + f (x + k))) (≤-+ (succ (inc f (x + k) + f (x + k))) (f (succ (x + k)))))

-- we devide by 2 and take the remaining value
 div₂ : (y : ℕ) → ℕ × 𝟚
 div₂ zero = zero , ₀
 div₂ (succ y) = let (x , prf) = div₂ y in case prf of λ { ₀ → x , ₁ ; ₁ → succ x , ₀}

 _+₂_ : 𝟚 → 𝟚 → 𝟚
 _+₂_ ₀ y = y
 _+₂_ ₁ ₀ = ₁
 _+₂_ ₁ ₁ = ₀

 intV-h : (q : 𝟚) → (f g : ℕ → ℕ) → (h : ℕ) → (v : ℕ × 𝟚) → IV (q +₂ (v .pr₂))
 intV-h ₁ f g h (r , ₀) = [ f r , f (succ r) ] (g r)
 intV-h ₁ f g h (r , ₁) = f (succ r) [ g r , g (succ r) ]
 intV-h ₀ f g h (r , ₀) = f r  [ g r , g (succ r) ]
 intV-h ₀ f g h (r , ₁) = [ f r , f (succ r) ]  g (succ r)

 intV : (q : 𝟚) → (ℕ → ℕ) → (ℕ → ℕ) → (h : ℕ) → IV (q +₂ (div₂ h .pr₂))
 intV q f g h = intV-h q f g h (div₂ h)

 _at_ : Fn ⟨ fc ⟩ → ℕ → Fn ⟨ fc ⟩
 (a , pa , fca) at zero = a , pa , fca
 (a , pa , fca) at succ n = ((fc ⟶) a) at n
  

--  Liveness1 : (&PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) → &PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) → 𝓣 ̇) → PotSet₂ 𝓣
--  Liveness1 {𝓣 = 𝓣} R a b = (iv : 𝟚 × Σ Increasing × Σ Increasing) → (n : ℕ) → Σ k ꞉ ℕ , n ≤ k × rr iv k where
--    rra : (k : ℕ) → (r : 𝟚) → IV r → 𝓣 ̇
--    rra k t (x [ y1 , y2 ]) = Σ m ꞉ ℕ , (m ≤ y2) × (y1 ≤ m) × R ((a at x) .pr₂ .pr₁) ((b at m) .pr₂ .pr₁)
--    rra k t ([ x2 , x1 ] y) = Σ m ꞉ ℕ , (m ≤ x2) × (x1 ≤ m) × R ((a at m) .pr₂ .pr₁) ((b at y) .pr₂ .pr₁)
--    rr : (iv : Σ (λ x → Σ Increasing × Σ Increasing)) → (k : ℕ) → 𝓣 ̇
--    rr (q , f , g) k = rra k (q +₂ (div₂ k .pr₂)) (intV q < f > < g > k)

```
