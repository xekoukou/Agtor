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

module Equality (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) (dec : (a b : Secret) → is-decidable (a ＝ b)) {𝓥} {𝓦} {𝓣} where

open list-decidable dec

open PropositionalTruncation pt
open import UF.ImageAndSurjection pt

open import xBSet fe pt Msg Secret
open import &PSet (𝟚 × ×BSet (𝓤 ⊔ 𝓥)) pt
open import PSet pt (&PSet (𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦) × &PSet (𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦))
open import Scope fe pt Msg Secret

open import CoAlgebra fe pt UA Msg Secret {𝓤 ⊔ 𝓥} {𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦} {𝓤 ⁺⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣}
open import Operators fe pt UA Msg Secret dec {𝓥} {𝓦} {𝓣}



-- The universal property of the conaturals
-- According to Martin Escardo, they exist.

F∞ : 𝓤₀ ̇  → 𝓤₀ ̇
F∞ X = 𝟙 + X

Fm∞ : {X Y : 𝓤₀ ̇ } → (X → Y) → F∞ X → F∞ Y
Fm∞ f (inl x) = inl _
Fm∞ f (inr x) = inr (f x)

CoAlgebra∞ : (𝓤₀ ⁺) ̇
CoAlgebra∞ = Σ E ꞉ 𝓤₀ ̇ , (E → F∞ E)


module Eq (d : CoAlgebra∞) (suc : F∞ (d .pr₁) → d .pr₁) (fc : Final-CoAlgebra) (_∈?_ : ∀ s ls → is-decidable (s ∈ ls)) where

 open Op fc _∈?_

 ℕ∞ = d .pr₁
 pred = d .pr₂

 _≤∞_ : ℕ → ℕ∞ → 𝓤₀ ̇
 _≤∞_ zero s = 𝟙
 _≤∞_ (succ b) s = case (pred s) of l1 where
  l1 : _ → _
  l1 (inl x) = 𝟘
  l1 (inr x) = b ≤∞ x

 open co-F-co-iso fc

 open CoAlgebra
 open CoAlgebra-morphism

-- To construct a normal form, first we need to measure the number of stuttering steps.
-- We do this with universal property of N∞.
-- We find an k ∈ N∞ and then we need to construct a function F Q.E × N∞ → B where B is the information we need. This B function will be the variance we will introduce in our normal form.
 
 D : _
 D = F Q.E → F Q.E + 𝟙 {𝓤₀}


 Q : (f : D) → F Q.E → _
 Q f q@(p , nx , c , e) = l1 (f q) where
   l1 : _ → _
   l1 (inl x) = (c ＝ Q.f nx .pr₂ .pr₂ .pr₁) × (x ＝ Q.f nx)
   l1 (inr t) = ¬ (c ＝ Q.f nx .pr₂ .pr₂ .pr₁) × 𝟙 {_}




 ww : {!!}
 ww = Σ q ꞉ F Q.E , Σ n∞ ꞉ ℕ∞ , l1 q (pred n∞) where
  l1 : F Q.E → 𝟙 + ℕ∞ → {!!}
  l1 q (inl x) = {!!}
  l1 q (inr x) = {!!}







 r :  (n : ℕ) → (n∞ : ℕ∞) → n ≤∞ n∞ → F Q.E → PSet (𝓤 ⁺⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣)
 r zero _ ineq v@(p , nx , c , f) = p
 r (succ n) n∞ ineq v@(p , nx , c , f) with pred n∞
 ... | inr x = r n x ineq v


 r2 :  (n : ℕ) → (n∞ : ℕ∞) → n ≤∞ n∞ → F Q.E → ExC Q.E
 r2 zero _ ineq v@(p , nx , cf) = cf
 r2 (succ n) n∞ ineq v@(p , nx , c , f) with pred n∞
 ... | inr x = r2 n x ineq v


 Var-ExC : ∀ 𝓠 → _
 Var-ExC 𝓠 = Σ D ꞉ 𝓠 ̇  , (D → ExC Q.E)


 df : Var-ExC (𝓤 ⊔ 𝓥) → ExC Q.E
 df (D , f) = (xva , xvm) , λ x d → Q.uni ∣P'-co .pr₁ .pr₁ (l1 x d) where
  xva = Var→×BSet (D , λ d → f d .pr₁ .pr₁) 
  xvm = Var→×BSet (D , λ d → f d .pr₁ .pr₂) 
  l1 : (x : S×Msg) → ⟨ xva .pr₁ ⟩ x + ⟨ xvm .pr₁ ⟩ x → ExCG (𝓤 ⊔ 𝓥) (F Q.E)
  l1 x (inl y) = (Σ d ꞉ D , ⟨ f d .pr₁ .pr₁ .pr₁ ⟩ x) , λ (d , e) → Q.f (f d .pr₂ x (inl e))
  l1 x (inr y) = (Σ d ꞉ D , ⟨ f d .pr₁ .pr₂ .pr₁ ⟩ x) , λ (d , e) → Q.f (f d .pr₂ x (inr e))
