{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
import State

module FState {ℓ ℓ'} (C : ∀ n → Type ℓ) where

module St = State C
open St

record FFState (n : ℕ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  constructor FSt
  field 
    ⟨_⟩ : Type ℓ'
    fs : ⟨_⟩ → State n

open FFState


data FRel {n : ℕ} (fq1 : FFState n) : FFState n → Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  frel : {A : Type ℓ'} {f : A → ⟨ fq1 ⟩} → {g : ⟨ fq1 ⟩ → A} → retract f g → FRel fq1 (FSt A (fq1 .fs ∘ f))

open FRel

FState : ℕ → Type (ℓ-max ℓ (ℓ-suc ℓ'))
FState n = FFState n / FRel {n}

dd : ∀{n : ℕ} → {ffst1 ffst2 : FFState n} → (v1 : ⟨ ffst1 ⟩) → (r : FRel ffst1 ffst2) → ⟨ ffst2 ⟩
dd {_} {ffst1} v1 (frel {_} {f} {g} x) = g v1


data FDom {n : ℕ} : FState n → Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  vl : {ffst : FFState n} →  ⟨ ffst ⟩ → FDom [ ffst ]
  eqd : {ffst1 : FFState n} → {A : Type ℓ'} → (v2 : A) → {f : A → ⟨ ffst1 ⟩} → {g : ⟨ ffst1 ⟩ → A} → (rt : retract f g)
        → PathP (λ i → FDom (eq/ ffst1 (FSt A (ffst1 .fs ∘ f)) (frel {A = A} {f} {g} rt) i)) (vl (f v2)) (vl v2)
  sqd : ∀{ x y : FState n} → (p1 p2 : x ≡ y) → (dx : FDom x) → (dy : FDom y)
       → (dp1 : PathP (λ i → FDom (p1 i)) dx dy)
       → (dp2 : PathP (λ i → FDom (p2 i)) dx dy) → SquareP (λ i j → FDom (squash/ x y p1 p2 i j)) dp1 dp2 refl refl


_$_ : {n : ℕ} → (os : FState n) → FDom os → State n
.([ _ ]) $ vl {ffst} x = (fs ffst) x
.(eq/ _ (FSt _ (ffst1 .fs ∘ _)) (frel {_} {ffst1} {A} {f} {g} rt) i) $ eqd {ffst1} {A} v2 {f} {g} rt i = refl {x = ffst1 .fs (f v2)} i
.(squash/ _ _ p1 p2 i j) $ sqd {x} {y} p1 p2 dx dy dp1 dp2 i j = squash/ (x $ dx) (y $ dy) (cong₂ _$_ p1 dp1) (cong₂ _$_ p2 dp2) i j
