{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Base

open import Lists
open import Maybe

module PSet (pt : propositional-truncations-exist) (&PSet : 𝓥 ̇) where

open PropositionalTruncation pt


-- This predicate describes all the possible superpositions of a system.
record PSet 𝓦 : 𝓥 ⊔ 𝓦 ⁺ ̇  where
 field
  ∣⟨_⟩ : (o : &PSet) → 𝓦 ̇ 
  ∣-is-prop : ∀ o → is-prop (∣⟨_⟩ o)

open PSet public


module PSet-Op (_&-&ᵖ_ : &PSet → &PSet → &PSet) where
  
  _&ᵖ_ : PSet 𝓦 → PSet 𝓦 → PSet (𝓥 ⊔ 𝓦)
  ∣⟨ A &ᵖ B ⟩ o = ∥ Σ &A ꞉ &PSet , Σ &B ꞉ &PSet , ∣⟨ A ⟩ &A × ∣⟨ B ⟩ &B × (&A &-&ᵖ &B ＝ o)  ∥
  ((A &ᵖ B) .∣-is-prop) o = ∥∥-is-prop
  
  _∣ᵖ_ : PSet 𝓦 → PSet 𝓦 → PSet 𝓦
  ∣⟨ A ∣ᵖ B ⟩ o = ∥ ∣⟨ A ⟩ o + ∣⟨ B ⟩ o ∥
  ∣-is-prop (A ∣ᵖ B) o = ∥∥-is-prop
  
  
   -- TODO Is this the best way to describe this???
   -- Move this to the more specialized case where GSet is BSet
  -- _ᵀ : PSet → PSet 𝓦
  -- ∣⟨ A ᵀ ⟩ o
  -- = ∥ (∀ x → (p : ∣⟨ A ⟩ x) → Σ y ꞉ 𝟚 × BSet , &⟨ x ⟩ y × &⟨ o ⟩ (y ᵗ))
  --     × (∀ y → &⟨ o ⟩ y → Σ x ꞉ &PSet , (∣⟨ A ⟩ x) × &⟨ x ⟩ (y ᵗ) )
  --   ∥
  -- ∣-is-prop (A ᵀ) o = ∥∥-is-prop
  
  --- ?????
  --  _ᵀ : PSet 𝓦 → PSet 𝓦
  --  ∣⟨ A ᵀ ⟩ o = ∥ (∀ x → (p : ∣⟨ A ⟩ x) → Σ y ꞉ 𝟚 × BSet , &⟨ x ⟩ y × &⟨ o ⟩ (y ᵗ)) ∥
  --  ∣-is-prop (A ᵀ) o = ∥∥-is-prop
  
  Var : ∀ 𝓦 → (D : 𝓣 ̇ ) → 𝓥 ⊔ 𝓣 ⊔ 𝓦 ⁺ ̇
  Var {_} 𝓦 D = (D → PSet 𝓦)
  
  Var→PSet : {D : 𝓣 ̇ } → Var 𝓦 D → PSet (𝓣 ⊔ 𝓦)
  ∣⟨ Var→PSet {D = D} f ⟩ &ps = ∥ (Σ x ꞉ D , ∣⟨ f x ⟩ &ps) ∥
  ∣-is-prop (Var→PSet f) &ps = ∥∥-is-prop
  
  -- Dependent variance
  -- Here both systems change at the same time
  
  DVar : ∀ 𝓦 (D : 𝓣 ̇ ) → 𝓥 ⊔ 𝓣 ⊔ 𝓦 ⁺ ̇
  DVar 𝓦 D = (D → PSet 𝓦 × PSet 𝓦)
  
  -- Given a variance, we are not sure if we will have two systems or one.
  -- This depends on the variance itself.
  -- For example, one of the system might terminate.
  -- TODO I do not think I use this anymore
  -- pDVar : { D : 𝓤 ̇ } → 𝓤 ⁺⁺ ⁺ ̇
  -- pDVar {D} = (D → (𝟙+ PSet 𝓦) × PSet 𝓦)
  
  -- This is unaffected, since we compose the systems in different superpositions.
  ∣ᵈᵖ : { D : 𝓣 ̇ } → DVar 𝓦 D → PSet (𝓣 ⊔ 𝓦) 
  ∣ᵈᵖ {D} f = Var→PSet (pr₁ ∘ f) ∣ᵖ Var→PSet (pr₂ ∘ f)
  
  -- p∣ᵈᵖ : { D : 𝓤 ̇ } → pDVar {D} → PSet 𝓦
  -- p∣ᵈᵖ {D} f = Var→PSet λ d → pr₁ (f d) <p _∣ᵖ_ > pr₂ (f d)
  
  -- This on the other hand is affected. We
  -- cannot treat the systems as separate. They interact together.
  &ᵈᵖ : { D : 𝓣 ̇ } → DVar 𝓦 D → PSet (𝓥 ⊔ 𝓣 ⊔ 𝓦)
  &ᵈᵖ {D} f = Var→PSet (λ d → (pr₁ (f d)) &ᵖ (pr₂ (f d)))
  
  -- p&ᵈᵖ : { D : 𝓤 ̇ } → pDVar {D} → PSet 𝓦
  -- p&ᵈᵖ {D} f = Var→PSet (λ d → (pr₁ (f d)) <p _&ᵖ_ > (pr₂ (f d)))
