{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Maybe
open import Cubical.Data.Vec as V
open import Cubical.Data.List as L
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.List.Dependent

import State
open import State.Properties
open import Projection
open import Common

module ActorM {ℓ ℓ' : _} (prM : UMTypePr ℓ ℓ') where


open ProjStr (snd prM) public
UMType = ⟨ prM ⟩

-- This is the only relevant part when we check for subtypes.
-- Since subtypes, need to be true at each step of the reduction, independently of the other steps.
record  Pred (k : ℕ) : Type (ℓ-suc ℓ) where
  field
    -- The predicate relevant secrets, at the start.
    m : ℕ
    Pt  : UMType → Type
-- The new secrets, at the end.
    Pns : ℕ

open Pred



interleaved mutual

  -- A Particle is either a msg or an Actor.
  -- Both messages and actors have continuations, because we want to take the dual of an actor, which 
  -- needs to have a continuation.
  record ParticleT (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ'))

  module StT = State ParticleT

-- The continuation
  record PredContT (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    inductive
    field
      pred : Pred k
      decPt  : ∀ A → Dec ((Pt pred) A)
      secr : List (Fin (m pred))
      δᶜT : ∀ A → { p : ∥ (Pt pred) A ∥₁ } → ⟨ ⟦ A ⟧ ⟩ → StT.SState (k + (Pns pred))

  open PredContT
  
-- For the formulation of the subtype, the existence of δT guarantees the reduction.
-- but it is not zero, with regards to the bahavior type of the system.
-- δT needs to be removed for behavioral types.
  record ParticleT k where
    coinductive
    field
      δᶜTs : List (PredContT k)
      δT    : StT.SState k

  open ParticleT

interleaved mutual

  data Particle {k : ℕ} (Typ : ParticleT k) : Type (ℓ-suc (ℓ-max ℓ ℓ'))
  record Actor {k : ℕ} (Typ : ParticleT k) : Type (ℓ-suc (ℓ-max ℓ ℓ'))
  
  record Msg {k : ℕ} (Typ : ParticleT k) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    inductive
    field
      mtyp : UMType
      val  : ⟨ ⟦ mtyp ⟧ ⟩
      mpred : Pred k
      mcond : (Pt mpred) mtyp
      inPart : mpred ∈ (L.map PredContT.pred (δᶜTs Typ))

  module StV = State (λ k → (Σ (ParticleT k) Particle))

  data _withType_ : ∀{fv} → StV.SState fv → StT.SState fv → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))

  record PredCont {k : ℕ} (predC : PredContT k) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    inductive
    field
      δᶜ  : ∀ A → { p : ∥ (Pt (pred predC)) A ∥₁ } → (v : ⟨ ⟦ A ⟧ ⟩) → Σ (StV.SState (k + (Pns (pred predC)))) (_withType ((δᶜT predC) A {p} v))

  
  data Particle {k} Typ where
    msg : Msg Typ → Particle Typ
    actor : Actor Typ → Particle Typ

  record Actor {k} Typ where
    coinductive
    field
      δᶜs  : ListP PredCont (δᶜTs Typ)
      δ    : Σ (StV.SState k) (_withType (δT Typ))


  data _withType_ where
    wT0b : ∀{fv} → _withType_ {fv} StV.0b StT.0b
    wT1b : ∀{fv} → _withType_ {fv} StV.1b StT.1b
    _wT∪_ : ∀{fv} → ∀{v1 v2 t1 t2} → v1 withType t1 → v2 withType t2 → (v1 StV.∪ v2) withType (StT._∪_ {fv} t1 t2)
    _wT·_  : ∀{fv} → ∀{v1 v2 t1 t2} → v1 withType t1 → v2 withType t2
           → (v1 StV.· v2) withType (StT._·_ {fv} t1 t2)
    wTν_  : ∀{fv} → ∀{v t} → v withType t → (StV.ν_ {fv} v) withType (StT.ν t)
    wTᵃ  : ∀{fv k} → {secr : Vec (Fin fv) k} → ∀{ct}
           → (act : Actor ct) → (StV.[ secr ] (ct , actor act) StV.ᵃ) withType (StT.[ secr ] ct StT.ᵃ)
    wTᵐ  : ∀{fv k} → {secr : Vec (Fin fv) k} → ∀{ct}
           → (m : Msg ct) → (StV.[ secr ] (ct , msg m) StV.ᵐ) withType (StT.[ secr ] ct StT.ᵐ)

