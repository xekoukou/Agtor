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

module ActorM {ℓ ℓ' : _} (prM : UMTypePr ℓ ℓ') where


open ProjStr (snd prM) public
UMType = ⟨ prM ⟩


-- Msgs have a type and a number of new secrets.
-- New Secrets are at the start of the Vec.

record MsgT k : Type ℓ where
  field
    umT : UMType
    nsecr : Fin (suc k)


mutual

  data CT (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    ct-m : MsgT k → CT k
    ct-a : ActorT k → CT k

  module StT = State CT

  record ActorT (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    coinductive
    field
      minS    : List (Fin k)  -- This is the secrets that all messages must have
                              -- This is useful for local reduction purposes.
      P     : List (Fin k) → ℕ → UMType → Type
      decP  : ∀ c s A → Dec (P c s A)
      δᶜT   : ∀ c s A → { p : ∥ P c s A ∥₁ } → ⟨ ⟦ A ⟧ ⟩ → StT.SState (s + k)
      δT    : StT.SState k

mutual
  
  data C (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    c-m : (MT : MsgT k) → ⟨ ⟦ MsgT.umT MT ⟧ ⟩ → C k
    c-a : (AT : ActorT k) → Actor AT → C k

  module StV = State C

  record Actor {k : ℕ} (Typ : ActorT k) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    coinductive
    
    open ActorT
    
    field
      δᶜ  : ∀ c s A → { p : ∥ (P Typ) c s A ∥₁ } → (v : ⟨ ⟦ A ⟧ ⟩) → Σ (StV.SState (s + k)) (_withType (δᶜT Typ) c s A {p} v)
      δ   : Σ (StV.SState k) (_withType δT Typ)


  data _withType_ : ∀{fv} → StV.SState fv → StT.SState fv → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
    wT0b : ∀{fv} → _withType_ {fv} StV.0b StT.0b
    wT1b : ∀{fv} → _withType_ {fv} StV.1b StT.1b
    _wT∪_ : ∀{fv} → ∀{v1 v2 t1 t2} → v1 withType t1 → v2 withType t2 → (v1 StV.∪ v2) withType (StT._∪_ {fv} t1 t2)
    _wT·_  : ∀{fv} → ∀{v1 v2 t1 t2} → v1 withType t1 → v2 withType t2
           → (v1 StV.· v2) withType (StT._·_ {fv} t1 t2)
    wTν_  : ∀{fv} → ∀{v t} → v withType t → (StV.ν_ {fv} v) withType (StT.ν t)
    wT`  : ∀{fv k} → {secr : Vec (Fin fv) k} → ∀{c ct}
           → c withTypeC ct → (StV.` StV.[ secr ] c) withType (StT.` StT.[ secr ] ct)

  data _withTypeC_ {k} : C k → CT k → Type ((ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))) where
    wtCm : ∀{t v} → (c-m t v) withTypeC (ct-m t)
    wtCa : ∀{t a} → (c-a t a) withTypeC (ct-a t)
