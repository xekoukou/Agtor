{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Vec as V
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin


import State
open import State.Properties
open import Projection

module Definitions where

UMTypePr : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
UMTypePr ℓ ℓ' = Proj ℓ (SET ℓ')


module _ {ℓ ℓ' : _} (prM : UMTypePr ℓ ℓ') where

  open ProjStr (snd prM)
  UMType = ⟨ prM ⟩


  mutual

    CT : ℕ → Type (ℓ-suc (ℓ-max ℓ ℓ'))
    CT k = UMType ⊎ ActorT k

    module StT = State CT

    record ActorT (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      coinductive
      
      field
        P     : List (Fin k) → UMType → Type
        decP  : ∀ C A → Dec (P C A)
        δᶜT  : ∀ C A → { p : ∥ P C A ∥₁ } → ⟨ ⟦ A ⟧ ⟩ → StT.SState
        δT   : StT.SState



  -- ValM = Σ UMType λ A → ⟨ ⟦ A ⟧ ⟩

  -- mutual
    
  --   ValA : ℕ → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
  --   ValA k = Σ (ActorT k) (Actor {k})

  --   C : ℕ → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
  --   C k = ValM ⊎ ValA k

  --   _typ : ∀ {k} → C k → CT k
  --   inl x typ = inl (fst x)
  --   inr x typ = inr (fst x)

  --   module StV = State C

  --   record Actor {k : ℕ} (Typ : ActorT k) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  --     coinductive
      
  --     open ActorT
      
  --     field
  --       δᶜ  : ∀ A → { p : ∥ (P Typ) A ∥₁ } → ⟨ ⟦ A ⟧ ⟩ → StV.SState
  --       δ   : StV.SState


  -- record _∋ₐ_ {k} (T : ActorT k) (a : Actor T) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  --   open ActorT
  --   open Actor

  --   field
  --     δᶜᵀ : ∀ A → { p : ∥ (P T) A ∥₁ } → (v : ⟨ ⟦ A ⟧ ⟩)
  --       → StT.StrEq StT.⟨ mapₛ-StrSt _typ (StV.isStrSt ((δᶜ a) A {p} v)) ⟩ₛ ((δᶜT T) A {p} v)
  --     δᵀ : StT.StrEq StT.⟨ mapₛ-StrSt _typ (StV.isStrSt (δ a)) ⟩ₛ (δT T)


  -- _∋ₛ_ : StT.SState → StV.SState → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
  -- _∋ₛ_ T v = StT.StrEq StT.⟨ mapₛ-StrSt _typ (StV.isStrSt v) ⟩ₛ T


