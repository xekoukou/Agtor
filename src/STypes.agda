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
open import Cubical.HITs.SetQuotients as SQ renaming ([_] to ⟨_⟩ₛ)
-- import State
-- open import State.Lemma
-- import State.Properties
-- import ActorM
open import Projection
-- open import Common

module STypes {ℓ} (MsgP : ℕ → Type ℓ) (mpsuc : ∀{k} → MsgP k → MsgP (suc k)) where

open import BSet MsgP mpsuc

-- Provides a predicates on the msgs needed by the environment so that the term always reduces.

data SType (k : ℕ) : Type (ℓ-suc ℓ) where
  _ᵐ : BSet k → SType k
  _ᵃ : BSet k → SType k
  _&_ : (l r : SType k) → SType k
  _∣_ : (l r : SType k) → SType k
  μ_ : SType (suc k) → SType k


0ᵐ : ∀{k} → SType k
0ᵐ = ⊥B ᵐ

-- 0 ᵐ indicates that one reduction will always happen.
-- μ 0 ᵐ ≡ 0 ᵐ
-- 0 ᵐ & x ≡ 0 ᵐ
-- 0 ᵐ ∣ x ≡ x


μeG : ∀{k} → SType (suc k) → SType k
μeG (x ᵐ) = Bsucₚ x ᵐ
μeG (x ᵃ) = Bsucₚ x ᵃ
μeG (g & g₁) = μeG g & μeG g₁
μeG (g ∣ g₁) = μeG g ∣ μeG g₁
μeG (μ g) = μ μeG g

rmμ : ∀{k} → SType k → SType k
rmμ (x ᵐ) = x ᵐ
rmμ (x ᵃ) = x ᵃ
rmμ (g & g₁) = rmμ g & rmμ g₁
rmμ (g ∣ g₁) = rmμ g ∣ rmμ g₁
rmμ (μ g) = μeG g


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

data _G_ {k} : SType k → SType k → Type (ℓ-suc ℓ) where
  &ar : {L R : BSet k} → ((L ᵃ) & (R ᵃ)) G ((L || R) ᵃ)
  -- dual to previous
  |mr : {L R : BSet k} → ((L ᵐ) ∣ (R ᵐ)) G ((L || R) ᵐ)

--   not true since we can have two different messages x ∈ L ∧ y ∈ R but none in L ∧ R
--  &mr : {L R : BSet k} → ((L ᵃ) ∣ (R ᵃ)) G ((L && R) ᵃ)

--  &mr : {L R E : BSet k} → ⊨ ((L || R) ─→ E) → ⊨ (E ─→ (L || R)) → ((L ᵐ) & (R ᵐ)) G (E ᵐ)
--  -- If I introduce _ᵀ in SType, then the one is derivable from the second.
--  &ar : {L R E : BSet k} → ⊨ ((L && R) ─→ E) → ⊨ (E ─→ (L && R)) → ((L ᵃ) & (R ᵃ)) G (E ᵃ)
--  ∣mr : {L R E : BSet k} → ⊨ ((L || R) ─→ E) → ⊨ (E ─→ (L || R)) → ((L ᵐ) ∣ (R ᵐ)) G (E ᵐ)
--  -- If I introduce _ᵀ in SType, then the one is derivable from the second.
--  ∣ar : {L R E : BSet k} → ⊨ ((L || R) ─→ E) → ⊨ (E ─→ (L || R)) → ((L ᵃ) ∣ (R ᵃ)) G (E ᵃ)
--  0ᵐ& : {q : SType k} → (0ᵃ & q) G {!!}
--  0ᵐ∣ : {q : SType k} → {!!} G {!!}


-- A ⊑ B means that if reduction happens for B for Context C, then it will also happen for A.

data _G2_ {k} : SType k → SType k → Type (ℓ-suc ℓ) where
  G' : ∀ {m a : SType k} → m G a → m G2 a

  -- This is not useful for Behavior types, only for reduction types.
  -- cut is the only way to reduce the restrictions.
  cut : ∀ {m a : BSet k} → (((m || a) ᵐ) & (a ᵃ)) G2 ((m ᵐ) & (a ᵃ))
  cut` : ∀ {m a : BSet k} → (((m || a) ᵃ) ∣ (a ᵐ)) G2 ((m ᵃ) ∣ (a ᵐ))

  -- cut`` : ∀ {m a : BSet k} → ((m ᵐ) & ((a || m) ᵃ)) G2 ((m ᵐ) & (a ᵃ)) ----> wrong only one direction
  -- the correct direction follows from ←ₐ.



-- IMPORTANT : The dual operator reverses the relation, it seems.
data _⊑_ : {k : ℕ} → SType k → SType k → Type (ℓ-suc ℓ) where
  _→ₘ_ : {k : ℕ} → ∀ (l r : BSet k) → {mph : ⊨ (l ↦ r)} → (l ᵐ) ⊑ (r ᵐ)
  -- DUAL
  _←ₐ_ : {k : ℕ} → ∀ (l r : BSet k) → {mph : ⊨ (r ↦ l)} → (l ᵃ) ⊑ (r ᵃ)

  &mr  : {k : ℕ} →  ∀ (l r : BSet k) →  ((l ᵐ) & ( r ᵐ)) ⊑ ((l || r) ᵐ)
  -- DUAL
  |ar2 : {k : ℕ} → ∀ (l r : BSet k) →  ((l || r) ᵃ) ⊑ ((l ᵃ) ∣ (r ᵃ))

  -- this is a consequence of _→ₘ_ and |mr
  -- |mr :  ∀ (l r : BSet k) →  ((l && r) ᵐ) ⊑ ((l ᵐ) ∣ ( r ᵐ))
  -- its dual (l ᵃ) & (r ᵃ) ⊑ (l && r) ᵃ

  |ar  :  {k : ℕ} → ∀ (l r : BSet k) →  ((l ᵃ) ∣ ( r ᵃ)) ⊑ ((l && r) ᵃ)
  -- DUAL
  &mr2 : {k : ℕ} → ∀ (l r : BSet k) → ((l && r) ᵐ) ⊑ ((l ᵐ) & (r ᵐ))

  &r : {k : ℕ} → (l r : SType k) → (l & r) ⊑ l
  |rl : {k : ℕ} → (l r : SType k) → l ⊑ (l ∣ r)
  |rr : {k : ℕ} → (l r : SType k) → r ⊑ (l ∣ r)

  &r2 : {k : ℕ} → ∀(l1 l2 r1 r2 : SType k) → l1 ⊑ r1 → l2 ⊑ r2 → (l1 & l2) ⊑ (r1 & r2)
  |r2 : {k : ℕ} → ∀(l1 l2 r1 r2 : SType k) → l1 ⊑ r1 → l2 ⊑ r2 → (l1 ∣ l2) ⊑ (r1 ∣ r2)

-- This is derivable from  &ar and _←ₐ_
--   &r  :  ∀ (l r c : BSet k) → {mph : ⊨ ((l ─→ c) && (r  ─→ c)) } → (c ᵃ) ⊑ ((l ᵃ) & ( r ᵃ))

-- This is wrong
--   |r  :  ∀ (l r c : BSet k) → {mph : ⊨ ((l ─→ c) || (r  ─→ c)) } → (c ᵃ) ⊑ ((l ᵃ) ∣ ( r ᵃ))

-- lᵐ & r ᵐ ∣  (l && r) ᵐ

  -- μeG only contains msgs from the outside world, thus it exludes msgs that are internal to q, that could lead to reduction.
  μ2  : {k : ℕ} → ∀{q : SType (suc k)} → (μ q) ⊑ (μeG q)
  
  μ⊑  : {k : ℕ} → ∀{q e : SType (suc k)} → q ⊑ e → (μ q) ⊑ (μ e)
  -- Wrong : Consider q ⊑ e is less restrictive in both ends. And thus, we could add a term that reduces e , but not q, that is not taken into account
  -- because the restriction of μ, that only considers terms from the outside.
  -- μ⊑2  : ∀{q e : SType (suc k)} → (μ q) ⊑ (μ e) → q ⊑ e
  μ-cut : {k : ℕ} → ∀{a : BSet k} → {m : BSet (suc k)} → ((μ ((m || Bpredₚ a) ᵐ)) & (a ᵃ)) ⊑ ((μ (m ᵐ)) & (a ᵃ))
  μ-cut2 : {k : ℕ} → ∀{m : BSet k} → {a : BSet (suc k)} → ((μ (a ᵃ)) & ((m || Bsucₚ a) ᵐ)) ⊑ ((μ (a ᵃ)) & (m ᵐ))

cut2 : ∀{k} → ∀ {m a : SType k} → a ⊑ (m ᵀ) → (a & m) ⊑ 0ᵐ
cut2 {k} {x₁ ᵐ} {a} x = {!!}
cut2 {k} {x₁ ᵃ} {a} x = {!!}
cut2 {k} {m & m₁} {a} x = {!!}
cut2 {k} {m ∣ m₁} {a} x = {!!}
cut2 {k} {μ m} {a} x = {!!}



-- (a ᵐ & b ᵐ) & c ᵃ ----> (a || b) ᵐ  --- > this cannot work
-- since two x ∈ a and y ∈ b is different than z ∈ (a || b)
-- if a ─→ c but a || a || b ─→ c , then the first certainly reduces, while the other not sure.

-- (a ᵐ & b ᵐ) & c ᵃ ----> a ─→ c   a - c = 0 | b - c = 0
-- c ᵃ ⊑ a ᵃ | b ᵃ ----> a ─> c

-- (a ᵐ | b ᵐ) & c ᵃ ---> a ─→ c && b ─→ c
-- (a ᵐ | b ᵐ) ⊑ (a && b) ᵐ  -----> a && b ─→ c            a ─→ c & b ─→ c
-- c ᵃ ⊑ a ᵃ & b ᵃ  a ─→ c && b ─→ c --- CORRECT

-- (a ᵃ & b ᵃ) & c ᵐ ---> c ─→ (a || b) is more general than this c → a || c → b



-- (a ᵐ & b ᵐ) & c ᵃ ----> a ᵐ & b ᵐ & (c - a) ᵃ = 0ᵐ    --- c - (a ∨ b) = 0 --> (c -> a) ─→ c ─→ a ∣ b
-- a ᵃ ∣ b ᵃ ⊑ c ᵃ ------>   (a ∣ b) ᵃ ⊑ c ᵃ  -----> c ─→ (a ∣ b) ------>
-- c ᵐ ⊑ a ᵐ & b ᵐ ---> c → a | b
-- (a ᵐ | b ᵐ) & c ᵃ --->  c - a = 0 & c - b = 0
--- a ᵃ & b ᵃ ⊑ c ᵃ --> c ─→ a && b
--- c ᵐ ⊑ a ᵐ | b ᵐ ---> 




------- Maybe we cab transfrom non-determinism into determistic computation if ( a ᵐ | b ᵐ ) & (a ᵃ & b ᵃ) is transformed so that for the a ∧ b is empty. This can be done because of rule &ar, thus we can deal
-- with deterministic computation, and their properties, and then transform this to the non-deterministic case. This can be done, the question is how useful it can be.


-- BPred : ∀{k} → PredP k → BSet k
-- BPred {k} A MP =
--   let (n , rl) = nsecr (def MP)
--       (osecrm , nsecrm) = V.split (FD.fromℕ' _ n rl) (secr MP)
--       csecr = compSecr osecrm (secr A)
      
--   in (fst (nsecr (def MP)) ≡ Pns (def A)) × (csecr ≡ just (Ps (def A))) × Pt (def A) (umT (def MP))

-------------------------------------------------------------

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
projₘ (μ s) mp = projₘ (μeG s) mp

{-# TERMINATING #-}
projₐ : ∀{k} → SType k →  BSet k
projₐ (x ᵐ) mp = x mp
projₐ (x ᵃ) mp = Lift ⊥
projₐ (s & s₁) mp = projₐ s mp ⊎ projₐ s₁ mp
projₐ (s ∣ s₁) mp = projₐ s mp ⊎ projₐ s₁ mp
projₐ (μ s) mp = projₐ (μeG s) mp
