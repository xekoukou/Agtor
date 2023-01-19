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


open ProjStr (snd prM)
UMType = ⟨ prM ⟩

record Secret k : Type ℓ where
  field
    cond : UMType
    nsecr : ℕ
    secr : Vec (Fin k) nsecr


mutual

  data CT (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    ct-s : Secret k → CT k
    ct-m : UMType → CT k
    ct-a : ActorT k → CT k

  module StT = State CT

  record ActorT (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    coinductive
    field
      minS    : List (Fin k)  -- This is the secrets that all messages must have
                              -- This is useful for local reduction purposes.
      P     : List (Fin k) → UMType → Type
      decP  : ∀ C A → Dec (P C A)
      δᶜT   : ∀ C A → { p : ∥ P C A ∥₁ } → ⟨ ⟦ A ⟧ ⟩ → Σ (StT.SState) λ s → StT.WellScopedₛₛ s k
      δT    : Σ (StT.SState) λ s → StT.WellScopedₛₛ s k

      δᶜTs   : ∀{m} → ∀ C → (S : Secret m) → { p : ∥ P C (Secret.cond S) ∥₁ } → ActorT (Secret.nsecr S + k)

mutual
  
  data C (k : ℕ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    c-s : Secret k → C k
    c-m : (MT : UMType) → ⟨ ⟦ MT ⟧ ⟩ → C k
    c-a : (AT : ActorT k) → Actor AT → C k

  module StV = State C

  record Actor {k : ℕ} (Typ : ActorT k) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    coinductive
    
    open ActorT
    
    field
      δᶜ  : ∀ C A → { p : ∥ (P Typ) C A ∥₁ } → (v : ⟨ ⟦ A ⟧ ⟩) → Σ StV.SState (_withType fst ((δᶜT Typ) C A {p} v))
      δ   : Σ StV.SState (_withType fst (δT Typ))
      δᶜs   : ∀{m} → ∀ C → (S : Secret m) → { p : ∥ (P Typ) C (Secret.cond S) ∥₁ } → Actor ((δᶜTs Typ) C S {p})


  data _withType_ : StV.SState → StT.SState → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
    wT0b : StV.0b withType StT.0b
    wT1b : StV.1b withType StT.1b
    wT∪  : ∀{v1 v2 t1 t2} → (v1 StV.∪ v2) withType (t1 StT.∪ t2)
    wT·  : ∀{v1 v2 t1 t2} → (v1 StV.· v2) withType (t1 StT.· t2)
    wTν  : ∀{v t} → (StV.ν v) withType (StT.ν t)
    wT`  : ∀{k} → {secr : Vec ℕ k} → ∀{c ct} → c withTypeC ct → (StV.` StV.[ secr ] c) withType (StT.` StT.[ secr ] ct)

  data _withTypeC_ {k} : C k → CT k → Type ((ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))) where
    wtCs : ∀{s} → (c-s s) withTypeC (ct-s s)
    wtCm : ∀{t v} → (c-m t v) withTypeC (ct-m t)
    wtCa : ∀{t a} → (c-a t a) withTypeC (ct-a t)
