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
open import Cubical.Data.Vec as V
open import Cubical.Data.List as L
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin

import State
open import State.Properties
open import Projection

module ActorM {ℓ ℓ' : _} (prM : UMTypePr ℓ ℓ') where


open ProjStr (snd prM) public
UMType = ⟨ prM ⟩

record TypPred (k : ℕ) : Type (ℓ-suc ℓ) where
  field
    Pt  : UMType → Type
    decPt  : ∀ A → Dec (Pt A)
    Ps  : List (Fin k)
    Pns : ℕ

open TypPred



-- Msgs have a type and a number of new secrets.
-- New Secrets are at the start of the Vec.

record MsgT k : Type ℓ where
  field
    umT : UMType
    nsecr : Fin (suc k)


interleaved mutual

  record ActorT (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ'))

  data CT (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    ct-m : MsgT k → CT k
    ct-a : ActorT k → CT k

  module StT = State CT


  record δᶜT-Section (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    inductive
    field
      typPred : TypPred k
      δᶜT : ∀ A → { p : ∥ (Pt typPred) A ∥₁ } → ⟨ ⟦ A ⟧ ⟩ → StT.SState (k + (Pns typPred))

  record ActorT k where
    coinductive
    field
      δᶜTs : List (δᶜT-Section k)
      δT    : StT.SState k

mutual
  
  data C (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    c-m : (MT : MsgT k) → ⟨ ⟦ MsgT.umT MT ⟧ ⟩ → C k
    c-a : (AT : ActorT k) → Actor AT → C k

  module StV = State C

  record δᶜ-Section (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    inductive
    open δᶜT-Section
    field
      δᶜTsec : δᶜT-Section k
      δᶜ  : ∀ A → { p : ∥ (Pt (typPred δᶜTsec)) A ∥₁ } → (v : ⟨ ⟦ A ⟧ ⟩) → Σ (StV.SState (k + (Pns (typPred δᶜTsec)))) (_withType ((δᶜT δᶜTsec) A {p} v))



  record Actor {k : ℕ} (Typ : ActorT k) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    coinductive
    
    open ActorT Typ
    
    field
      δᶜTs  : Σ (List (δᶜ-Section k)) (_withδᶜTs δᶜTs)
      δ   : Σ (StV.SState k) (_withType δT)


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

  data _withδᶜTs_ {k} (ls : List (δᶜ-Section k)) : List (δᶜT-Section k) → Type ((ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))) where
    wtδᶜ : ls withδᶜTs L.map δᶜ-Section.δᶜTsec ls  
