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

module SType {ℓ} (MsgP : ℕ → Type ℓ) (mpsuc : ∀{k} → MsgP k → ℕ → MsgP (suc k)) where

open import BSet MsgP mpsuc

-- Predicates on msgs that represent a single actor or a single msg

data SType (k : ℕ) : Type (ℓ-suc ℓ) where
  _ᵐ : BSet k → SType k
  _ᵃ : BSet k → SType k
  _&_ : (l r : SType k) → SType k
  _∣_ : (l r : SType k) → SType k
  μ_ : SType (suc k) → SType k


-- A predicate that is true for no msgs.
-- Its existence though means that there is such a message.

0ᵐ : ∀{k} → SType k
0ᵐ = ⊥B ᵐ

-- A predicate that is true for all msgs
-- its existence means that all msgs can be consumed.

1ᵃ : ∀{k} → SType k
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

_ᵀ : ∀{k} → SType k → SType k
(x ᵐ) ᵀ = x ᵃ
(x ᵃ) ᵀ = x ᵐ
(g & g₁) ᵀ = (g ᵀ) ∣ (g₁ ᵀ)
(g ∣ g₁) ᵀ = (g ᵀ) & (g₁ ᵀ)
(μ g) ᵀ = μ (g ᵀ)

dTT : ∀{k} → (g : SType k) → (g ᵀ) ᵀ ≡ g
dTT (x ᵐ) = refl
dTT (x ᵃ) = refl
dTT (g & g₁) = cong₂ _&_ (dTT g) (dTT g₁)
dTT (g ∣ g₁) = cong₂ _∣_ (dTT g) (dTT g₁)
dTT (μ g) = cong μ_ (dTT g)

-- r ᵀ must be the maximal context element under which r reduces.
-- TODO PROVE THIS
-- cut is inconsequential here because cut relation is biderctional.



-- A ⊑ B means that if reduction happens for B for Context C, then it will also happen for A.

-- IMPORTANT : The dual operator reverses the relation, it seems.
data _⊑_ : {k : ℕ} → SType k → SType k → Type (ℓ-suc ℓ) where
  refl⊑ :{k : ℕ} → (r : SType k) →  r ⊑ r
  trans⊑ : {k : ℕ} → (r l m : SType k) → r ⊑ l → l ⊑ m → r ⊑ m

  _→ₘ_ : {k : ℕ} → ∀ (l r : BSet k) → {mph : ⊨ (l ↦ r)} → (l ᵐ) ⊑ (r ᵐ)
  -- DUAL
  _←ₐ_ : {k : ℕ} → ∀ (l r : BSet k) → {mph : ⊨ (r ↦ l)} → (l ᵃ) ⊑ (r ᵃ)

  &r1 : {k : ℕ} → (l r : SType k) → (l & r) ⊑ l
  |r1 : {k : ℕ} → (l r : SType k) → l ⊑ (l ∣ r)

  &r2 : {k : ℕ} → ∀(l1 l2 r1 r2 : SType k) → l1 ⊑ r1 → l2 ⊑ r2 → (l1 & l2) ⊑ (r1 & r2)
  |r2 : {k : ℕ} → ∀(l1 l2 r1 r2 : SType k) → l1 ⊑ r1 → l2 ⊑ r2 → (l1 ∣ l2) ⊑ (r1 ∣ r2)

  &ar1 : ∀{k} → {L R : BSet k} → ((L ᵃ) & (R ᵃ)) ⊑ ((L || R) ᵃ)
  &ar2 : ∀{k} → {L R : BSet k} → ((L || R) ᵃ) ⊑ ((L ᵃ) & (R ᵃ))

  |mr1 : ∀{k} → {L R : BSet k} → ((L ᵐ) ∣ (R ᵐ)) ⊑ ((L || R) ᵐ)
  |mr2 : ∀{k} → {L R : BSet k} → ((L || R) ᵐ) ⊑ ((L ᵐ) ∣ (R ᵐ)) 

  -- Because of →ₘ , we can avoid  using (m ─ a).
  cut1 : {k : ℕ} → ∀ {m a : BSet k} → (((m || a) ᵐ) & (a ᵃ)) ⊑ ((m ᵐ) & (a ᵃ))

  -- DUAL to previous
  cut2 : {k : ℕ} → ∀ {m a : BSet k} → ((a ᵃ) ∣ (m ᵐ)) ⊑ (((a || m) ᵃ) ∣ (m ᵐ))

  μ⊑  : {k : ℕ} → ∀{q e : SType (suc k)} → q ⊑ e → (μ q) ⊑ (μ e)


cu : ∀{k} → ∀ {m a : SType k} → a ⊑ (m ᵀ) → (a & m) ⊑ ((m ᵀ) & m)
cu {_} {m} {a} x = &r2 a m (m ᵀ) m x (refl⊑ m)

-- Maybe just introduce this rule and cut the equations in half??
-- TODO
dd : ∀{k} → ∀ {m a : SType k} → a ⊑ m → (m ᵀ) ⊑ (a ᵀ)
dd {_} {m} {.m} (refl⊑ .m) = refl⊑ (m ᵀ)
dd {_} {.(r ᵐ)} {.(l ᵐ)} (_→ₘ_ l r {mph}) = _←ₐ_ r l {mph = mph}
dd {_} {.(r ᵃ)} {.(l ᵃ)} (_←ₐ_ l r {mph}) = _→ₘ_ r l {mph = mph}
dd {_} {m} {.(m & r)} (&r1 .m r) = |r1 (m ᵀ) (r ᵀ)
dd {_} {.(a ∣ r)} {a} (|r1 .a r) = &r1 (a ᵀ) (r ᵀ)
dd {_} {.(r1 & r2)} {.(l1 & l2)} (&r2 l1 l2 r1 r2 ieq ieq₁) = |r2 (r1 ᵀ) (r2 ᵀ) (l1 ᵀ) (l2 ᵀ) (dd ieq) (dd ieq₁)
dd {_} {.(r1 ∣ r2)} {.(l1 ∣ l2)} (|r2 l1 l2 r1 r2 ieq ieq₁) = &r2 (r1 ᵀ) (r2 ᵀ) (l1 ᵀ) (l2 ᵀ) (dd ieq) (dd ieq₁)
dd {_} {.((_ || _) ᵃ)} {.((_ ᵃ) & (_ ᵃ))} &ar1 = |mr2
dd {_} {.((_ ᵃ) & (_ ᵃ))} {.((_ || _) ᵃ)} &ar2 = |mr1
dd {_} {.((_ || _) ᵐ)} {.((_ ᵐ) ∣ (_ ᵐ))} |mr1 = &ar2
dd {_} {.((_ ᵐ) ∣ (_ ᵐ))} {.((_ || _) ᵐ)} |mr2 = &ar1
dd {_} {.((_ ᵐ) & (_ ᵃ))} {.(((_ || _) ᵐ) & (_ ᵃ))} cut1 = cut2
dd {_} {.(((_ || _) ᵃ) ∣ (_ ᵐ))} {.((_ ᵃ) ∣ (_ ᵐ))} cut2 = cut1
dd {_} {.(μ _)} {.(μ _)} (μ⊑ ieq) = μ⊑ (dd ieq)
dd {_} {m} {a} (trans⊑ .a l .m ieq1 ieq2) = trans⊑ _ _ _ (dd ieq2) (dd ieq1)

-- a ᵀ is the maximal context under which a reduces.
-- This looks like a universal property.
ee : ∀{k} → ∀ {m a : SType k} → a ⊑ (m ᵀ) → m ⊑ (a ᵀ)
ee {_} {m} x = subst (λ v → v ⊑ _) (dTT m) (dd x)


μeG : ∀{k} → SType (suc k) → ℕ → SType k
μeG (x ᵐ) n = Bsucₚ x n ᵐ
μeG (x ᵃ) n = Bsucₚ x n ᵃ
μeG (g & g₁) n = μeG g n & μeG g₁ n
μeG (g ∣ g₁) n = μeG g n ∣ μeG g₁ n
μeG (μ g) n = μ μeG g (suc n)





-- Projections for their use in Coevolution
-- In essence in coevolution, we do not care about superposition | or for &.
-- For this to work , we need to make sure that we always have reduction, thus the term is not stuck.
-- this is possible with the use of STypes, in other words we cannot close a term t with μ / ν unless some conditions are met.
-- For all cases, we have reduction.


{-# TERMINATING #-}
projₘ : ∀{k} → SType k →  BSet k
projₘ (x ᵐ) mp = x mp
projₘ (x ᵃ) mp = Lift ⊥
projₘ (s & s₁) mp = projₘ s mp ⊎ projₘ s₁ mp
projₘ (s ∣ s₁) mp = projₘ s mp ⊎ projₘ s₁ mp
projₘ (μ s) mp = projₘ (μeG s 0) mp

{-# TERMINATING #-}
projₐ : ∀{k} → SType k →  BSet k
projₐ (x ᵐ) mp = x mp
projₐ (x ᵃ) mp = Lift ⊥
projₐ (s & s₁) mp = projₐ s mp ⊎ projₐ s₁ mp
projₐ (s ∣ s₁) mp = projₐ s mp ⊎ projₐ s₁ mp
projₐ (μ s) mp = projₐ (μeG s 0) mp
