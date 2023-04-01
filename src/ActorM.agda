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
import Cubical.Data.List as L
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
  data ParticleT (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ'))

  module StT = State ParticleT

-- The continuation
  record PredContT (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    coinductive
    field
      pred : Pred k
      decPt  : ∀ A → Dec ((Pt pred) A)
      δᶜT : ∀ A → { p : ∥ (Pt pred) A ∥₁ } → ⟨ ⟦ A ⟧ ⟩ → StT.SState (k + (Pns pred))

  open PredContT
  
-- For the formulation of the subtype, the existence of δT guarantees the reduction.
-- but it is not zero, with regards to the bahavior type of the system.
-- δT needs to be removed for behavioral types.
  data ParticleT k where
    δᶜTP : PredContT k → ParticleT k
    δTP  : StT.SState k → ParticleT k

  open ParticleT

interleaved mutual

  data Particle {k : ℕ} : (Typ : ParticleT k) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  
  record Msg {k : ℕ} (Typ : PredContT k) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    inductive
    field
      mtyp : UMType
      val  : ⟨ ⟦ mtyp ⟧ ⟩
      mcond : (Pt (pred Typ)) mtyp

  module StV = State (λ k → (Σ (ParticleT k) Particle))

  data _withType_ : ∀{fv} → StV.SState fv → StT.SState fv → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))

  record PredCont {k : ℕ} (predC : PredContT k) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    coinductive
    field
      δᶜ  : ∀ A → { p : ∥ (Pt (pred predC)) A ∥₁ } → (v : ⟨ ⟦ A ⟧ ⟩) → Σ (StV.SState (k + (Pns (pred predC)))) (_withType ((δᶜT predC) A {p} v))

  
  data Particle {k} Typ where
    msg : ∀{p} → Msg p → Particle (δᶜTP p)
    actorδᶜ : ∀{p} → PredCont p → Particle (δᶜTP p)
    actorδ  : ∀{p} → (v : StV.SState k) → (v withType p) → Particle (δTP p)

  data acTyp {fv} : StV.SParticle fv → StT.SParticle fv → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
    a[] : acTyp L.[] L.[]
    aδ : ∀{k sv sf} → {secr : Vec (Fin fv) k} → {p : StT.SState k} → (v : StV.SState k) → (e : v withType p) → acTyp sv sf → acTyp (State.[ secr ] ((δTP p) , (actorδ v e)) L.∷ sv) ((StT.[ secr ] δTP p) L.∷ sf)
    aδᶜ : ∀{k sv sf} → {secr : Vec (Fin fv) k} → {p : PredContT k} → (v : PredCont p) → acTyp sv sf
         → acTyp (State.[ secr ] ((δᶜTP p) , actorδᶜ v) L.∷ sv) ((StT.[ secr ] δᶜTP p) L.∷ sf)

  data mTyp {fv} : StV.SParticle fv → StT.SParticle fv → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
    m[] : mTyp L.[] L.[]
    mδᶜ : ∀{k sv sf} → {secr : Vec (Fin fv) k} → {p : PredContT k} → (v : Msg p) → mTyp sv sf
         → mTyp (State.[ secr ] ((δᶜTP p) , msg v) L.∷ sv) ((StT.[ secr ] δᶜTP p) L.∷ sf)


  data _withType_ where
    wT0b : ∀{fv} → _withType_ {fv} StV.0b StT.0b
    wT1b : ∀{fv} → _withType_ {fv} StV.1b StT.1b
    _wT∪_ : ∀{fv} → ∀{v1 v2 t1 t2} → v1 withType t1 → v2 withType t2 → (v1 StV.∪ v2) withType (StT._∪_ {fv} t1 t2)
    _wT·_ : ∀{fv} → ∀{v1 v2 t1 t2} → v1 withType t1 → v2 withType t2
            → (v1 StV.· v2) withType (StT._·_ {fv} t1 t2)
    wTν_ : ∀{fv} → ∀{v t} → v withType t → (StV.ν_ {fv} v) withType (StT.ν t)
    wTᵃ  : ∀{fv sv sf} → acTyp {fv} sv sf → (sv StV.ᵃ) withType (sf StT.ᵃ)
    wTᵐ  : ∀{fv sv sf} → mTyp {fv} sv sf → (sv StV.ᵐ) withType (sf StT.ᵐ)

  
