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
open import Cubical.Core.Id hiding (_≡_)
open import Cubical.Data.Sigma
open import Cubical.Data.Vec as V
import Cubical.Data.List as L
open import Cubical.Data.Maybe
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
open import Projection

module SType2 {ℓ} (Msg : Type ℓ) where

open import BSet2 Msg

-- Predicates on msgs that represent a single actor or a single msg

data SType : Type (ℓ-suc ℓ) where
  _ᵐ : BSet → SType
  _ᵃ : BSet → SType
  _&_ : (l r : SType) → SType
  _∣_ : (l r : SType) → SType


-- A predicate that is true for no msgs.
-- Its existence though means that there is such a message.

0ᵐ : SType
0ᵐ = ⊥B ᵐ

-- A predicate that is true for all msgs
-- its existence means that all msgs can be consumed.

1ᵃ : SType
1ᵃ = ⊤B ᵃ

-- 0ᵐ & r ᵃ  reduces always
-- 1ᵃ & m ᵐ  reduces always
-- m ᵃ & m ᵐ reduces always
-- 1ᵃ & m ᵐ ⊑ m ᵃ & m ᵐ


-- Reduction means the consumption of one message for sure, thus any reduction will need to be of the form
-- 0ᵐ & r ᵃ & g and due to r& 0ᵐ & r ᵃ
-- thus proving reduction is equivalent to proving that s ⊑ 0ᵐ & r ᵃ

-- By definition, reduction of a in context m happens when a ⊑ m ᵀ
-- TODO show that this is the more general concept.

_ᵀ : SType → SType
(x ᵐ) ᵀ = x ᵃ
(x ᵃ) ᵀ = x ᵐ
(g & g₁) ᵀ = (g ᵀ) ∣ (g₁ ᵀ)
(g ∣ g₁) ᵀ = (g ᵀ) & (g₁ ᵀ)

dTT : (g : SType) → (g ᵀ) ᵀ ≡ g
dTT (x ᵐ) = refl
dTT (x ᵃ) = refl
dTT (g & g₁) = cong₂ _&_ (dTT g) (dTT g₁)
dTT (g ∣ g₁) = cong₂ _∣_ (dTT g) (dTT g₁)

-- r ᵀ must be the maximal context element under which r reduces.
-- TODO PROVE THIS
-- cut is inconsequential here because cut relation is biderctional.



-- A ⊑ B means that if reduction happens for B for Context C, then it will also happen for A.

-- IMPORTANT : The dual operator reverses the relation, it seems.
data _⊑_ : SType → SType → Type (ℓ-suc ℓ) where
  refl⊑ : (r : SType) →  r ⊑ r
  trans⊑ : (r l m : SType) → r ⊑ l → l ⊑ m → r ⊑ m

  _→ₘ_ : ∀ (l r : BSet) → {mph : ⊨ (l ↦ r)} → (l ᵐ) ⊑ (r ᵐ)
  -- DUAL
  _←ₐ_ : ∀ (l r : BSet) → {mph : ⊨ (r ↦ l)} → (l ᵃ) ⊑ (r ᵃ)

  &r1 : (l r : SType) → (l & r) ⊑ l
  |r1 : (l r : SType) → l ⊑ (l ∣ r)

  &r2 : ∀(l1 l2 r1 r2 : SType) → l1 ⊑ r1 → l2 ⊑ r2 → (l1 & l2) ⊑ (r1 & r2)
  |r2 : ∀(l1 l2 r1 r2 : SType) → l1 ⊑ r1 → l2 ⊑ r2 → (l1 ∣ l2) ⊑ (r1 ∣ r2)

  &ar1 : {L R : BSet} → ((L ᵃ) & (R ᵃ)) ⊑ ((L || R) ᵃ)
  &ar2 : {L R : BSet} → ((L || R) ᵃ) ⊑ ((L ᵃ) & (R ᵃ))

  |mr1 : {L R : BSet} → ((L ᵐ) ∣ (R ᵐ)) ⊑ ((L || R) ᵐ)
  |mr2 : {L R : BSet} → ((L || R) ᵐ) ⊑ ((L ᵐ) ∣ (R ᵐ)) 

  -- Because of →ₘ , we can avoid  using (m ─ a).
  cut1 : ∀ {m a : BSet} → (((m || a) ᵐ) & (a ᵃ)) ⊑ ((m ᵐ) & (a ᵃ))

  -- DUAL to previous
  cut2 : ∀ {m a : BSet} → ((a ᵃ) ∣ (m ᵐ)) ⊑ (((a || m) ᵃ) ∣ (m ᵐ))



cu : ∀ {m a : SType} → a ⊑ (m ᵀ) → (a & m) ⊑ ((m ᵀ) & m)
cu {m} {a} x = &r2 a m (m ᵀ) m x (refl⊑ m)

-- Maybe just introduce this rule and cut the equations in half??
-- TODO
dd : ∀ {m a : SType} → a ⊑ m → (m ᵀ) ⊑ (a ᵀ)
dd {m} {.m} (refl⊑ .m) = refl⊑ (m ᵀ)
dd {.(r ᵐ)} {.(l ᵐ)} (_→ₘ_ l r {mph}) = _←ₐ_ r l {mph = mph}
dd {.(r ᵃ)} {.(l ᵃ)} (_←ₐ_ l r {mph}) = _→ₘ_ r l {mph = mph}
dd {m} {.(m & r)} (&r1 .m r) = |r1 (m ᵀ) (r ᵀ)
dd {.(a ∣ r)} {a} (|r1 .a r) = &r1 (a ᵀ) (r ᵀ)
dd {.(r1 & r2)} {.(l1 & l2)} (&r2 l1 l2 r1 r2 ieq ieq₁) = |r2 (r1 ᵀ) (r2 ᵀ) (l1 ᵀ) (l2 ᵀ) (dd ieq) (dd ieq₁)
dd {.(r1 ∣ r2)} {.(l1 ∣ l2)} (|r2 l1 l2 r1 r2 ieq ieq₁) = &r2 (r1 ᵀ) (r2 ᵀ) (l1 ᵀ) (l2 ᵀ) (dd ieq) (dd ieq₁)
dd {.((_ || _) ᵃ)} {.((_ ᵃ) & (_ ᵃ))} &ar1 = |mr2
dd {.((_ ᵃ) & (_ ᵃ))} {.((_ || _) ᵃ)} &ar2 = |mr1
dd {.((_ || _) ᵐ)} {.((_ ᵐ) ∣ (_ ᵐ))} |mr1 = &ar2
dd {.((_ ᵐ) ∣ (_ ᵐ))} {.((_ || _) ᵐ)} |mr2 = &ar1
dd {.((_ ᵐ) & (_ ᵃ))} {.(((_ || _) ᵐ) & (_ ᵃ))} cut1 = cut2
dd {.(((_ || _) ᵃ) ∣ (_ ᵐ))} {.((_ ᵃ) ∣ (_ ᵐ))} cut2 = cut1
dd {m} {a} (trans⊑ .a l .m ieq1 ieq2) = trans⊑ _ _ _ (dd ieq2) (dd ieq1)

-- a ᵀ is the maximal context under which a reduces.
-- This looks like a universal property.
ee : ∀ {m a : SType} → a ⊑ (m ᵀ) → m ⊑ (a ᵀ)
ee {m} {a} x = subst (λ v → v ⊑ _) (dTT m) (dd x)


-- Projections for their use in Coevolution
-- In essence in coevolution, we do not care about superposition | or for &.
-- For this to work , we need to make sure that we always have reduction, thus the term is not stuck.
-- this is possible with the use of STypes, in other words we cannot close a term t with μ / ν unless some conditions are met.
-- For all cases, we have reduction.


projₘ : SType →  BSet
projₘ (x ᵐ) mp = x mp
projₘ (x ᵃ) mp = Lift ⊥
projₘ (s & s₁) mp = projₘ s mp ⊎ projₘ s₁ mp
projₘ (s ∣ s₁) mp = projₘ s mp ⊎ projₘ s₁ mp

projₐ : SType →  BSet
projₐ (x ᵐ) mp = x mp
projₐ (x ᵃ) mp = Lift ⊥
projₐ (s & s₁) mp = projₐ s mp ⊎ projₐ s₁ mp
projₐ (s ∣ s₁) mp = projₐ s mp ⊎ projₐ s₁ mp
