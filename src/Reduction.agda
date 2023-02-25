{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Vec as V
import Cubical.Data.List as L
open import Cubical.Data.Maybe
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin
import Cubical.Data.FinData as FD
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients as SQ renaming ([_] to ⟨_⟩ₛ)
import State
import State.Properties
import ActorM
open import Projection

module Reduction {ℓ ℓ' : _} (prM : UMTypePr ℓ ℓ') where

open ActorM prM

open StV
open MsgT
open ActorT
open Actor

open State.Properties.1C C


data ΔValue : ∀{fv} → SState fv → Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  V-0 : ∀{fv} → ΔValue {fv} 0b
  V-1 : ∀{fv} → ΔValue {fv} 1b
  V-m : ∀{fv k} → {secr : Vec (Fin fv) k} → {MT : MsgT k} → {msg : ⟨ ⟦ umT MT ⟧ ⟩} → ΔValue {fv} (` [ secr ] c-m MT msg)
  V-a : ∀{fv k} → {secr : Vec (Fin fv) k} → {AT : ActorT k} → {a : Actor AT}
        → Is0bₛₛ (fst (δ a)) → ΔValue {fv} (` [ secr ] c-a AT a)

infix 4 _—→_

data _—→_ : ∀{fvo fvt} → State fvo → State fvt → Type (ℓ-suc (ℓ-max ℓ ℓ')) where

