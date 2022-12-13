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

-- TODO We need to show distributed equality of identities
-- Let us say that we have one actor with a specific type.
-- We need to make sure that the protocol interacts with exactly this actor with this type.
-- thus we need to know that at this level, its identity is the same across
-- all the actors that it interacts with, in this specific level of abastraction.


-- TODO Since we are dealing with a distributed system, we canot guarantee that the actor will acto correctly based on its type.
-- thus type checking needs to be checked at runtime, thus all its values need to be stored for further inspection at this specific level of abstraction.
-- This can been by all participants storing those values or having a global place to store them all. I think the second case can be better.

import State

module Definitions where

module _ {ℓ} (UMType : Type ℓ) where

  mutual
  
    CT : ℕ → Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
    CT k = UMType ⊎ ActorT k

    module ST = State CT

    [CT] : Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
    [CT] = Σ _ λ k → Vec ℕ k × CT k

    PT : Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
    PT = ST.State → Type

    DPT : PT → Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
    DPT P = ∀ A → Dec (P A)



    record ActorT (k : ℕ) : Type (ℓ-max ℓ (ℓ-suc ℓ-zero)) where
      coinductive
      field
        q : ActorT 3
--        P : PT
--        decP : DPT P
        -- This projections needs to agree with the global projection function.
        -- I just can't fix this without abstracting the projection function here.
  --      {prJ} : ∀ A → ∥ P A ∥₁ → Type
     --   δᶜT : ∀ A → (c : ∥ P A ∥₁) → prJ A c → ST.State
     --   δT : ST.State


  mutual
  
    record Actor k : Type {!!} where
      inductive
      field
        type : ActorT k
        
        δ : State.State C

    -- Here for the second case, we have some form of parametricity with regards to ls. TODO
    C : ∀ k → Type {!!}
    C k = (Σ Type λ A → A) ⊎ (Actor k)

    record Case {k} : Type {!!} where
      field
 --       δᶜ : ∀ A → (c : ConT A (ptr cs)) → (prJ cs) A c → State.State C


    
    



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


