{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Nat


import State

module Definitions where

module _ {ℓ} (UMType : Type ℓ) (UAType : (k : ℕ) → Type ℓ) where

  CT : ℕ → Type ℓ
  CT = λ k → UMType ⊎ UAType k

  [CT] : ∀{k} → Type ℓ
  [CT] {k} = Vec ℕ k × CT k

  PT : Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  PT = ∀{k} → [CT] {k} → Type

  DPT : PT → Type ℓ
  DPT P = ∀{k} → ∀ A → Dec (P {k} A)

  Pattern : ∀ k → Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  Pattern k = Vec (Σ PT DPT) k

  ConT : ∀{k} → Vec [CT] (suc k) → Pattern (suc k) → Type
  ConT (l ∷ []) (f ∷ []) = ∥ fst f l ∥₁
  ConT (l ∷ ls@(_ ∷ _)) (f ∷ fs) = ∥ fst f l ∥₁ × ConT ls fs

  module St = State CT

  open St

  
  mutual
    
    record ActorT {k} (ls : Vec ℕ k) : Type {!!} where
    

    record Actor {k} {ls : Vec ℕ k} (Typ : ActorT ls) : Type {!!} where

    
