{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Sum
open import Cubical.Data.Vec as V
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Nat


import State

module Definitions where

module _ {ℓ} (UMType : Type ℓ) (UAType : (k : ℕ) → Type ℓ) where

  CT : ℕ → Type ℓ
  CT = λ k → UMType ⊎ UAType k

  [CT] : Type ℓ
  [CT] = Σ _ λ k → Vec ℕ k × CT k

  PT : Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  PT = [CT] → Type

  DPT : PT → Type ℓ
  DPT P = ∀ A → Dec (P A)

-- When a group of actors, messages is needed to produce a response, the predicate can
-- only be pointwise, because the checking of the predicate is distributed and pointwis, because the
-- receiving actor itself is distributed.

  Pattern : ∀ k → Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  Pattern k = Vec (Σ PT DPT) k

  ConT : ∀{k} → Vec [CT] (suc k) → Pattern (suc k) → Type
  ConT (l ∷ []) (f ∷ []) = ∥ fst f l ∥₁
  ConT (l ∷ ls@(_ ∷ _)) (f ∷ fs) = ∥ fst f l ∥₁ × ConT ls fs



  module St = State CT

  open St renaming (State to StateT)

  record CaseT {k} (ls : Vec ℕ k) : Type (ℓ-max ℓ (ℓ-suc ℓ-zero)) where
    field
      {d} : ℕ
      ptr : Pattern (suc d)
      -- This projections needs to agree with the global projection function.
      -- I just can't fix this without abstracting the projection function here.
      {prJ} : ∀ A → ConT A ptr → Type
      δᶜT : ∀ A → (c : ConT A ptr) → prJ A c → StateT
        
  record Case {k} {ls : Vec ℕ k} (cs : CaseT {k} ls) : Type {!!} where
    field
 --     δᶜ : ∀ A → (c : ConT A ptr) → prJ A c → State



  record ActorT {k} (ls : Vec ℕ k) : Type (ℓ-max ℓ (ℓ-suc ℓ-zero)) where
    coinductive
    field
      cases : List (CaseT ls)
      δT : StateT


  mutual
  
    record Actor {k} {ls : Vec ℕ k} (typ : ActorT ls) : Type {!!} where

    record Actor' {k} (ls : Vec ℕ k) : Type {!!} where
      field
        typ' : ActorT ls
        actor : Actor {k} {ls} typ'

    C : ∀ k → Type {!!}
    C k = {!!} 
    



  PrT : {⟦_⟧ : [CT] → Type} → ∀{k} → Vec [CT] (suc k) → Type
  PrT {⟦_⟧} (x ∷ []) = ⟦ x ⟧
  PrT {⟦_⟧} (x ∷ ls@(_ ∷ _)) = ⟦ x ⟧ × PrT {⟦_⟧} ls

  -- mutual 
  --   record Proj : Type {!!} where
  --     field
  --       prM : UMType → Type
  --       prA : ∀{k} → UAType k → (ls : Vec ℕ k) → ActorT {λ { (k , vs , inl x) → prM x
  --                                                          ; (k , vs , inr x) → {!Actor {k} {vs} ?!}}} ls


  --   -- prCT : {pr : Proj} → [CT] → Type
  --   -- prCT {pr} (k , vs , inl x) = (Proj.prM pr) x
  --   -- prCT {pr} (k , vs , inr x) = Actor


