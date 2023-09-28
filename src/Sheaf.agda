{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Core.Id hiding (_≡_)
open import Cubical.Data.Sigma
open import Cubical.Data.Vec as V
import Cubical.Data.List as L
import Cubical.Data.Maybe
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin
open import Cubical.Data.List
import Cubical.Data.FinData as FD
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients as SQ renaming ([_] to ⟨_⟩ₛ)

module Sheaf {ℓ}  (Msg : Type ℓ) where

open import BSet2 Msg
open import SType2 Msg

data _∈_ {ℓ} {A : Type ℓ} (y : A) : List A → Type ℓ where
  here : ∀{xs} → y ∈ (y ∷ xs)
  there : ∀{x xs} →  y ∈ xs → y ∈ (x ∷ xs)

-- Add the whole set and the empty  set.
record Topology (U : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Ind : Type ℓ
    openSet : Ind → (U → Type ℓ)
    union : ∀(PI : Ind → Type ℓ) → Σ Ind λ j → openSet j ≡ λ x → Σ Ind λ i → (PI i) × openSet i x
    intersection : (ls : List Ind) → Σ Ind λ j → openSet j ≡ λ x → ∀ i → i ∈ ls → openSet i x
    

record FinTopology (U : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Ind : Type ℓ
    oSet : Ind → (U → Type ℓ)
    union : (ls : List Ind) → Σ Ind λ j → oSet j ≡ λ x → Σ Ind λ i → i ∈ ls → oSet i x
    intersection : (ls : List Ind) → Σ Ind λ j → oSet j ≡ λ x → ∀ i → i ∈ ls → oSet i x
  

open FinTopology


-- Decidable predicates are closed under finite union and intersection
-- thus they form a FinTopology

<_>_⊂_ : ∀{U} → (fT : FinTopology U) →  (W V : Ind fT) → Type ℓ
< fT > W ⊂ V = ∀ x → oSet fT W x → oSet fT V x

⊂-trans : ∀{U} → {fT : FinTopology U} →  {W V D : Ind fT} → < fT > W ⊂ V → < fT > V ⊂ D → < fT > W ⊂ D
⊂-trans e r x cond = r x (e x cond)

record Cover {U} {fT : FinTopology U} (V : Ind fT) : Type (ℓ-suc ℓ) where
  field
    PI : Ind fT → Type ℓ
    subs : ∀ Uc → PI Uc → < fT > Uc ⊂ V
    isCov : ∀ x → oSet fT V x → Σ (Ind fT) λ Uc → PI Uc × oSet fT Uc x

open Cover

⊂refl : ∀{U} → (fT : FinTopology U) → ∀{W} → < fT > W ⊂ W
⊂refl ft W x = x

-- The decidable predicates form a Finite topology

record PreSheaf (U : Type ℓ) (A : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    fT : FinTopology U
    F : ∀ (W : Ind fT) → Type ℓ
    rstr : ∀{W V} → < fT > W ⊂ V → F V → F W
    -- is Functor
    rstr-id : ∀{W} → rstr {W} (⊂refl fT) ≡ λ x → x
    rstr-comp : ∀{W V R} → (W⊂V : < fT > W ⊂ V) → (V⊂R : < fT > V ⊂ R) →  ∀ x → rstr W⊂V (rstr V⊂R x) ≡ rstr (⊂-trans {fT = fT} W⊂V V⊂R) x


-- open PreSheaf

-- record  SSheaf (U : Type ℓ) (A : Type ℓ) (_*_ : A → A → A) : Type {!!} where
--   field
--     isPSf : PreSheaf U A
--     locallity : (V : Ind (fT isPSf)) → (cov : Cover {fT = fT isPSf} V)
--                 → (s1 s2 : F isPSf V) → ∀ W → (pw : PI cov W) → rstr isPSf (subs cov W pw) s1 ≡ rstr isPSf (subs cov W pw) s2
--     gluing : (ls : List (Σ (Ind (fT isPSf)) (F isPSf))) → (gl : F isPSf (fst (union (fT isPSf) (L.map fst ls))))
