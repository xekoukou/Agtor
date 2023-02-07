{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation

module StateLemma where

suc≤? : ℕ → ℕ → ℕ
suc≤? zero k = suc k
suc≤? (suc n) zero = zero
suc≤? (suc n) (suc k) = suc (suc≤? n k)

lsuc : ∀{n} → ℕ → Vec ℕ n → Vec ℕ n
lsuc {zero} n ls = []
lsuc {suc _} n (x ∷ ls) = suc≤? n x ∷ lsuc n ls

lemma1' : ∀ n m x → m ≤ n → suc≤? (suc n) (suc≤? m x) ≡ suc≤? m (suc≤? n x)
lemma1' n zero x rel = refl
lemma1' (suc n) (suc m) zero rel = refl
lemma1' (suc n) (suc m) (suc x) rel = cong suc (lemma1' n m x rel)

lemma1 : ∀{k} → ∀ n m ls → m ≤ n → lsuc {k} (suc n) (lsuc m ls) ≡ lsuc m (lsuc n ls)
lemma1 n m [] rel = refl
lemma1 n m (x ∷ ls) rel = cong₂ _∷_ (lemma1' n m x rel) (lemma1 n m ls rel)

