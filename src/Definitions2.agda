{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Sum

open import Projection2
import Poly

module Definitions2 where

UMTypePr : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
UMTypePr ℓ ℓ' = Proj ℓ (SET ℓ')

module _ {ℓ ℓ' : _} (prM : UMTypePr ℓ ℓ') where

  open ProjStr (snd prM)
  private
    UMType = ⟨ prM ⟩

  ValT = Σ UMType λ A → ⟨ ⟦ A ⟧ ⟩ 

  record ActorT : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    coinductive
    open Poly ActorT UMType
  
    field
      P     : UMType → Type
      decP  : ∀ A → Dec (P A)
      δᶜT  : ∀ A → { p : P A } → ⟨ ⟦ A ⟧ ⟩ → Poly
      δT   : Poly

  PolyT = Poly.Poly ActorT UMType

 
  open ActorT
  mutual

    PolyV = Poly.Poly Actor ValT

    record PrimActor (actT : ActorT) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      inductive
      field
        δᶜ  : ∀ A → { p : (P actT) A } → ⟨ ⟦ A ⟧ ⟩ → PolyV
        δ   : PolyV

    record Actor : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      constructor act
      inductive
      
      field
        T : ActorT
        poly : PolyV ⊎ PrimActor T 
  
  
  open Poly

  data _∈t_ : PolyV → PolyT → Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    0bT   : _∈t_ 0b 0b
    1bT   : _∈t_ 1b 1b
    _←T_  : (AT : ActorT) (MT : UMType) (body : PolyV ⊎ (PrimActor AT)) (v : ⟨ ⟦ MT ⟧ ⟩) → _∈t_ (act AT body ← (MT , v)) (AT ← MT)
    _∪Tl_ : ∀{PV PT1 PT2} → _∈t_ PV PT1 → _∈t_ PV (PT1 ∪ PT2)
    _∪Tr_ : ∀{PV PT1 PT2} → _∈t_ PV PT2 → _∈t_ PV (PT1 ∪ PT2)
    _∪T_ : ∀{PV1 PV2 PT1 PT2} → _∈t_ PV1 PT1 → _∈t_ PV2 PT2 → _∈t_ (PV1 ∪ PV2) (PT1 ∪ PT2)
    _·T_  : ∀{PV1 PV2 PT1 PT2} → _∈t_ PV1 PT1 → _∈t_ PV2 PT2 → _∈t_ (PV1 · PV2) (PT1 · PT2) 

  data _≤t_ : PolyT → PolyT → Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    ≡T   : ∀{t} → _≤t_ t t
    _∪Tl_ : ∀{PV PT1 PT2} → _≤t_ PV PT1 → _≤t_ PV (PT1 ∪ PT2)
    _∪Tr_ : ∀{PV PT1 PT2} → _≤t_ PV PT2 → _≤t_ PV (PT1 ∪ PT2)
    _∪T_ : ∀{PV1 PV2 PT1 PT2} → _≤t_ PV1 PT1 → _≤t_ PV2 PT2 → _≤t_ (PV1 ∪ PV2) (PT1 ∪ PT2)
    _·T_  : ∀{PV1 PV2 PT1 PT2} → _≤t_ PV1 PT1 → _≤t_ PV2 PT2 → _≤t_ (PV1 · PV2) (PT1 · PT2) 
