{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as M renaming (nothing to ∅ ; just to ⟦_⟧)
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
open import SemiRing

module State2 where

data Ordered¬∅ : ℕ → Set where
  1■ : Ordered¬∅ (suc zero)
  0:_ : ∀{n} → Ordered¬∅ n → Ordered¬∅ n
  1:_ : ∀{n} → Ordered¬∅ n → Ordered¬∅ (suc n)
  
Ordered : ℕ → Type
Ordered zero = Unit
Ordered (suc n) = Ordered¬∅ (suc n)

lsuc' : ∀{n} → ℕ → Ordered¬∅ n → Ordered¬∅ n
lsuc' zero ls = 0: ls
lsuc' (suc n) 1■ = 1■
lsuc' (suc n) (0: ls) = 0: lsuc' n ls
lsuc' (suc n) (1: ls) = 1: lsuc' n ls

lsuc : ∀{n} → ℕ → Ordered n → Ordered n
lsuc {zero} n tt = tt
lsuc {suc _} n ls = lsuc' n ls

lemma1' : ∀{k} → ∀ n m ls → m ≤ n → lsuc' {k} (suc n) (lsuc' m ls) ≡ lsuc' m (lsuc' n ls)
lemma1' zero zero ls rel = refl
lemma1' (suc n) zero ls rel = refl
lemma1' (suc n) (suc m) 1■ rel = refl
lemma1' (suc n) (suc m) (0: ls) rel = cong 0:_ (lemma1' n m ls rel)
lemma1' (suc n) (suc m) (1: ls) rel = cong 1:_ (lemma1' n m ls rel)

lemma1 : ∀{k} → ∀ n m ls → m ≤ n → lsuc {k} (suc n) (lsuc m ls) ≡ lsuc m (lsuc n ls)
lemma1 {zero} n m tt rel = refl
lemma1 {suc _} n m ls rel = lemma1' n m ls rel


-- data _∈_ : ℕ → Ordered → Type where
--   here■ : zero ∈ ⟦ 1■ ⟧
--   here: : ∀{ls} → zero ∈ ⟦ 1: ls ⟧
--   there1: : ∀{n ls} → n ∈ ⟦ ls ⟧ → (suc n) ∈ ⟦ 1: ls ⟧ 
--   there0: : ∀{n ls} → n ∈ ⟦ ls ⟧ → (suc n) ∈ ⟦ 0: ls ⟧ 
-- 
-- rem : ∀{n ol} →  n ∈ ol → Ordered
-- rem {.zero} {.(⟦ 1■ ⟧)} here■ = ∅
-- rem {.zero} {(⟦ 1: ol ⟧)} here: = ⟦ 0: ol ⟧
-- rem {.(suc _)} {.(⟦ 1: _ ⟧)} (there1: rel) = M.rec ⟦ 1■ ⟧ (⟦_⟧ ∘ 1:_) (rem rel)
-- rem {.(suc _)} {.(⟦ 0: _ ⟧)} (there0: rel) = M.rec ∅ (⟦_⟧ ∘ 0:_) (rem rel)
-- 
-- data _⊃_ (ol : Ordered) : List ℕ → Type where
--   more : ∀{n ns} → (rel : n ∈ ol) → rem rel ⊃ ns → ol ⊃ (n ∷ ns) 
--   none : ol ⊃ []
--

private
  variable
    ℓ : Level

infixr 5 _∪_
infixr 7 _·_
infixr 10 `_

module _ (C : ∀{n} → Vec ℕ n → Type ℓ) where

  mutual
  
    data State : Type ℓ where  
      0b      : State
      1b      : State
      `[_]_   : ∀{k} → (ls : Ordered k) → (∀ ls → C {k} ls) → State
      _∪_     : State → State → State 
      _·_     : State → State → State
      ν_      : State → State
      ν-elim  : ∀ q → ν (sucₛ 0 q) ≡ q
      ν-∪  : ∀ z q → ν (z ∪ (sucₛ 0 q)) ≡ (ν z) ∪ q
      ν-·  : ∀ z q → ν (z · (sucₛ 0 q)) ≡ (ν z) · q
      squash  : isSet (State)
      assoc   : (x y z : State) → (x ∪ (y ∪ z)) ≡ ((x ∪ y) ∪ z)
      rid     : (x : State) → x ∪ 0b ≡ x
      comm    : (x y : State) → x ∪ y ≡ y ∪ x
-- Equal terms here mean that we have equal state, but maybe we can have different actors (locationwise),
-- This also means that actors that the secret of ν does not play a role in the equality here.
-- In other words, as long as the structure is the same, it is the same state.
      idem    : (x : State) → x ∪ x ≡ x
      assoc·   : (x y z : State) → x · (y · z) ≡ (x · y) · z
      rid·     : (x : State) → x · 1b ≡ x
      comm·    : (x y : State) → x · y ≡ y · x
      def∅·   : (x : State) → x · 0b ≡ 0b
      dist    : (x y z : State) → x · (y ∪ z) ≡ (x · y) ∪ (x · z)

    {-# TERMINATING #-}
    sucₛ : ℕ → (q : State) → State
    sucₛ n 0b = 0b
    sucₛ n 1b = 1b
    sucₛ n (`[ ls ] x) = `[ lsuc n ls ] x
    sucₛ n (q ∪ q₁) = sucₛ n q ∪ sucₛ n q₁
    sucₛ n (q · q₁) = sucₛ n q · sucₛ n q₁
    sucₛ n (ν q) = ν sucₛ (suc n) q
    sucₛ n (ν-elim q i) = (cong ν_ (lemma2 n 0 q tt) ∙ ν-elim (sucₛ n q)) i
    sucₛ n (squash q q₁ x y i i₁) = squash (sucₛ n q) (sucₛ n q₁) (cong (sucₛ n) x) (cong (sucₛ n) y) i i₁
    sucₛ n (assoc q q₁ q₂ i) = assoc (sucₛ n q) (sucₛ n q₁) (sucₛ n q₂) i
    sucₛ n (rid q i) = rid (sucₛ n q) i
    sucₛ n (comm q q₁ i) = comm (sucₛ n q) (sucₛ n q₁) i
    sucₛ n (idem q i) = idem (sucₛ n q) i
    sucₛ n (assoc· q q₁ q₂ i) = assoc· (sucₛ n q) (sucₛ n q₁) (sucₛ n q₂) i
    sucₛ n (rid· q i) = rid· (sucₛ n q) i
    sucₛ n (comm· q q₁ i) = comm· (sucₛ n q) (sucₛ n q₁) i
    sucₛ n (def∅· q i) = def∅· (sucₛ n q) i
    sucₛ n (dist q q₁ q₂ i) = dist (sucₛ n q) (sucₛ n q₁) (sucₛ n q₂) i
    sucₛ n (ν-∪ q q₁ i) = (cong (λ a → ν (sucₛ (suc n) q ∪ a)) (lemma2 n 0 q₁ tt) ∙ (ν-∪ (sucₛ (suc n) q) (sucₛ n q₁))) i
    sucₛ n (ν-· q q₁ i) = (cong (λ a → ν (sucₛ (suc n) q · a)) (lemma2 n 0 q₁ tt) ∙ (ν-· (sucₛ (suc n) q) (sucₛ n q₁))) i



    lemma2 : ∀ n m q → m ≤ n → sucₛ (suc n) (sucₛ m q) ≡ sucₛ m (sucₛ n q)
    lemma2 n m 0b rel = refl
    lemma2 n m 1b rel = refl
    lemma2 n m (`[ ls ] x) rel = cong (`[_] x) (lemma1 n m ls rel)
    lemma2 n m (q ∪ q₁) rel = cong₂ _∪_ (lemma2 n m q rel) (lemma2 n m q₁ rel)
    lemma2 n m (q · q₁) rel = cong₂ _·_ (lemma2 n m q rel) (lemma2 n m q₁ rel)
    lemma2 n m (ν q) rel = cong ν_ (lemma2 (suc n) (suc m) q rel)
    lemma2 n m (ν-elim q i) rel = toPathP {A = (λ i → sucₛ (suc n) (sucₛ m (ν-elim q i)) ≡ sucₛ m (sucₛ n (ν-elim q i)))} {x = lemma2 n m (ν sucₛ 0 q) rel} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (ν-elim q i)) ≡ sucₛ m (sucₛ n (ν-elim q i))) i0 (lemma2 n m (ν sucₛ 0 q) rel)) (lemma2 n m q rel)) i
    lemma2 n m (squash q q₁ x y i i₁) rel = isOfHLevel→isOfHLevelDep 2 (λ a → isProp→isSet (squash (sucₛ (suc n) (sucₛ m a)) (sucₛ m (sucₛ n a)))) (lemma2 n m q rel) (lemma2 n m q₁ rel) (cong (λ d → lemma2 n m d rel) x) (cong (λ d → lemma2 n m d rel) y) (squash q q₁ x y) i i₁
    lemma2 n m (assoc q q₁ q₂ i) rel = toPathP {A = λ i → sucₛ (suc n) (sucₛ m (assoc q q₁ q₂ i)) ≡ sucₛ m (sucₛ n (assoc q q₁ q₂ i))} {x = cong₂ _∪_ (lemma2 n m q rel) (cong₂ _∪_ (lemma2 n m q₁ rel) (lemma2 n m q₂ rel))} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (assoc q q₁ q₂ i)) ≡ sucₛ m (sucₛ n (assoc q q₁ q₂ i))) i0 (cong₂ _∪_ (lemma2 n m q rel) (cong₂ _∪_ (lemma2 n m q₁ rel) (lemma2 n m q₂ rel)))) (cong₂ _∪_ (cong₂ _∪_ (lemma2 n m q rel) (lemma2 n m q₁ rel)) (lemma2 n m q₂ rel))) i
    lemma2 n m (rid q i) rel = toPathP {A = λ i → sucₛ (suc n) (sucₛ m (rid q i)) ≡ sucₛ m (sucₛ n (rid q i))} {x = cong₂ _∪_ (lemma2 n m q rel) refl} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (rid q i)) ≡ sucₛ m (sucₛ n (rid q i))) i0 (cong₂ _∪_ (lemma2 n m q rel) refl)) (lemma2 n m q rel)) i
    lemma2 n m (comm q q₁ i) rel = toPathP {A = λ i → sucₛ (suc n) (sucₛ m (comm q q₁ i)) ≡ sucₛ m (sucₛ n (comm q q₁ i))} {x = cong₂ _∪_ (lemma2 n m q rel) (lemma2 n m q₁ rel)} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (comm q q₁ i)) ≡ sucₛ m (sucₛ n (comm q q₁ i))) i0 (cong₂ _∪_ (lemma2 n m q rel) (lemma2 n m q₁ rel))) (cong₂ _∪_ (lemma2 n m q₁ rel) (lemma2 n m q rel))) i
    lemma2 n m (idem q i) rel = toPathP {A = λ i → sucₛ (suc n) (sucₛ m (idem q i)) ≡ sucₛ m (sucₛ n (idem q i))} {x = cong₂ _∪_ (lemma2 n m q rel) (lemma2 n m q rel)} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (idem q i)) ≡ sucₛ m (sucₛ n (idem q i))) i0 (cong₂ _∪_ (lemma2 n m q rel) (lemma2 n m q rel))) (lemma2 n m q rel)) i
    lemma2 n m (assoc· q q₁ q₂ i) rel = toPathP {A = λ i → sucₛ (suc n) (sucₛ m (assoc· q q₁ q₂ i)) ≡ sucₛ m (sucₛ n (assoc· q q₁ q₂ i))} {x = cong₂ _·_ (lemma2 n m q rel) (cong₂ _·_ (lemma2 n m q₁ rel) (lemma2 n m q₂ rel))} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (assoc· q q₁ q₂ i)) ≡ sucₛ m (sucₛ n (assoc· q q₁ q₂ i))) i0 (cong₂ _·_ (lemma2 n m q rel) (cong₂ _·_ (lemma2 n m q₁ rel) (lemma2 n m q₂ rel)))) (cong₂ _·_ (cong₂ _·_ (lemma2 n m q rel) (lemma2 n m q₁ rel)) (lemma2 n m q₂ rel))) i
    lemma2 n m (rid· q i) rel = toPathP {A = λ i → sucₛ (suc n) (sucₛ m (rid· q i)) ≡ sucₛ m (sucₛ n (rid· q i))} {x = cong₂ _·_ (lemma2 n m q rel) refl} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (rid· q i)) ≡ sucₛ m (sucₛ n (rid· q i))) i0 (cong₂ _·_ (lemma2 n m q rel) refl)) (lemma2 n m q rel)) i
    lemma2 n m (comm· q q₁ i) rel = toPathP {A = λ i → sucₛ (suc n) (sucₛ m (comm· q q₁ i)) ≡ sucₛ m (sucₛ n (comm· q q₁ i))} {x = cong₂ _·_ (lemma2 n m q rel) (lemma2 n m q₁ rel)} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (comm· q q₁ i)) ≡ sucₛ m (sucₛ n (comm· q q₁ i))) i0 (cong₂ _·_ (lemma2 n m q rel) (lemma2 n m q₁ rel))) (cong₂ _·_ (lemma2 n m q₁ rel) (lemma2 n m q rel))) i
    lemma2 n m (def∅· q i) rel = toPathP {A = λ i → sucₛ (suc n) (sucₛ m (def∅· q i)) ≡ sucₛ m (sucₛ n (def∅· q i))} {x = cong₂ _·_ (lemma2 n m q rel) refl} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (def∅· q i)) ≡ sucₛ m (sucₛ n (def∅· q i))) i0 (cong₂ _·_ (lemma2 n m q rel) refl)) refl) i
    lemma2 n m (dist q q₁ q₂ i) rel = toPathP {A = λ i → sucₛ (suc n) (sucₛ m (dist q q₁ q₂ i)) ≡ sucₛ m (sucₛ n (dist q q₁ q₂ i))} {x = cong₂ _·_ (lemma2 n m q rel) (cong₂ _∪_ (lemma2 n m q₁ rel) (lemma2 n m q₂ rel))} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (dist q q₁ q₂ i)) ≡ sucₛ m (sucₛ n (dist q q₁ q₂ i))) i0 (cong₂ _·_ (lemma2 n m q rel) (cong₂ _∪_ (lemma2 n m q₁ rel) (lemma2 n m q₂ rel)))) (cong₂ _∪_ (cong₂ _·_ (lemma2 n m q rel) (lemma2 n m q₁ rel)) (cong₂ _·_ (lemma2 n m q rel) (lemma2 n m q₂ rel)))) i
    lemma2 n m (ν-∪ q q₁ i) rel = toPathP {A = λ i → sucₛ (suc n) (sucₛ m (ν-∪ q q₁ i)) ≡ sucₛ m (sucₛ n (ν-∪ q q₁ i))} {x = cong ν_ (cong₂ _∪_ (lemma2 (suc n) (suc m) q rel) (lemma2 (suc n) (suc m) (sucₛ 0 q₁) rel))} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (ν-∪ q q₁ i)) ≡ sucₛ m (sucₛ n (ν-∪ q q₁ i))) i0 (cong ν_ (cong₂ _∪_ (lemma2 (suc n) (suc m) q rel) (lemma2 (suc n) (suc m) (sucₛ 0 q₁) rel)))) (cong₂ _∪_ (cong ν_ (lemma2 (suc n) (suc m) q rel)) (lemma2 n m q₁ rel))) i
    lemma2 n m (ν-· q q₁ i) rel = toPathP {A = λ i → sucₛ (suc n) (sucₛ m (ν-· q q₁ i)) ≡ sucₛ m (sucₛ n (ν-· q q₁ i))} {x = cong ν_ (cong₂ _·_ (lemma2 (suc n) (suc m) q rel) (lemma2 (suc n) (suc m) (sucₛ 0 q₁) rel))} (squash _ _ (transp (λ i → sucₛ (suc n) (sucₛ m (ν-· q q₁ i)) ≡ sucₛ m (sucₛ n (ν-· q q₁ i))) i0 (cong ν_ (cong₂ _·_ (lemma2 (suc n) (suc m) q rel) (lemma2 (suc n) (suc m) (sucₛ 0 q₁) rel)))) (cong₂ _·_ (cong ν_ (lemma2 (suc n) (suc m) q rel)) (lemma2 n m q₁ rel))) i


