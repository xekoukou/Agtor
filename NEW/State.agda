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
open import StateLemma

module State {ℓ} (C : (k : ℕ) → Type ℓ) where

infixr 5 _∪_
infixr 7 _·_
infixr 10 `[_]_

mutual
  
  data State : Type ℓ where  
    0b      : State
    1b      : State
    `[_]_   : ∀{k} → (ls : Vec ℕ k) → C k → State
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


module Elim {ℓ'} {B : State → Type ℓ'}
       (squash* : ∀ x → isSet (B x))
       (0b* : B 0b)
       (1b* : B 1b)
       (`[]* : ∀{k} → ∀ ls C → B (`[_]_ {k} ls C))
       (∪* : ∀{x y} → B x → B y → B (x ∪ y))
       (·* : ∀{x y} → B x → B y → B (x · y))
       (ν* : ∀{x} → B x → B (ν x))
       (ν-elim* : ∀ x → (b : B x) → (bs : B (sucₛ 0 x)) → PathP (λ i → B (ν-elim x i)) (ν* bs) b)
       (ν-∪* : ∀ x y → (bx : B x) → (by : B y) →  (bys : B (sucₛ 0 y)) → PathP (λ i → B (ν-∪ x y i)) (ν* (∪* bx bys)) (∪* (ν* bx) by))
       (ν-·* : ∀ x y → (bx : B x) → (by : B y) →  (bys : B (sucₛ 0 y)) → PathP (λ i → B (ν-· x y i)) (ν* (·* bx bys)) (·* (ν* bx) by))
       (assoc* : ∀ x y z → (bx : B x) → (by : B y) → (bz : B z) → PathP (λ i → B (assoc x y z i)) (∪* bx (∪* by bz)) (∪* (∪* bx by) bz))
       (rid* : ∀ x → (b : B x) → PathP (λ i → B (rid (x) i)) (∪* b 0b*) b)
       (comm* : ∀ x y → (bx : B x) → (by : B y) → PathP (λ i → B (comm (x) (y) i)) (∪* bx by) (∪* by bx))
       (idem* : ∀ x → (b : B x) → PathP (λ i → B (idem (x) i)) (∪* b b) b)
       (assoc·* : ∀ x y z → (bx : B x) → (by : B y) → (bz : B z) → PathP (λ i → B (assoc· (x) (y) (z) i)) (·* bx (·* by bz)) (·* (·* bx by) bz))
       (rid·* : ∀ x → (b : B x) → PathP (λ i → B (rid· x i)) (·* b 1b*) b)
       (comm·* : ∀ x y → (bx : B x) → (by : B y) → PathP (λ i → B (comm· (x) (y) i)) (·* bx by) (·* by bx))
       (def∅·* : ∀ x → (bx : B x) → PathP (λ i → B (def∅· (x) i)) (·* bx 0b*) 0b*)
       (dist* : ∀ x y z → (bx : B x) → (by : B y) → (bz : B z) → PathP (λ i → B (dist (x) (y) (z) i)) (·* bx (∪* by bz)) (∪* (·* bx by) (·* bx bz)))
       
       where
  {-# TERMINATING #-} 
  f : (x : State) → B x
  f 0b = 0b*
  f 1b = 1b*
  f (`[ ls ] C) = `[]* ls C
  f (x ∪ y) = ∪* (f x) (f y)
  f (x · y) = ·* (f x) (f y)
  f (squash a b p1 p2 i j) = isOfHLevel→isOfHLevelDep 2 squash*  (f a) (f b) (cong f p1) (cong f p2) (squash a b p1 p2) i j
  f (assoc x y z i) = assoc* x y z (f x) (f y) (f z) i
  f (rid x i) = rid* _ (f x) i
  f (comm x y i) = comm* x y (f x) (f y) i
  f (idem x i) = idem* (x) (f x) i
  f (assoc· x y z i) = assoc·* x y z (f x) (f y) (f z) i
  f (rid· x i) = rid·* _ (f x) i
  f (comm· x y i) = comm·* x y (f x) (f y) i
  f (def∅· x i) = def∅·* x (f x) i
  f (dist x y z i) = dist* x y z (f x) (f y) (f z) i
  f (ν q) = ν* (f q)
  f (ν-elim q i) = ν-elim* _ (f q) (f (sucₛ 0 q)) i
  f (ν-∪ q q₁ i) = ν-∪* q q₁ (f q) (f q₁) (f (sucₛ 0 q₁)) i
  f (ν-· q q₁ i) = ν-·* q q₁ (f q) (f q₁) (f (sucₛ 0 q₁)) i


module ElimProp {ℓ'} {B : State → Type ℓ'}
       (BProp : ∀{x} → isProp (B x))
       (0b* : B 0b)
       (1b* : B 1b)
       (`[]* : ∀{k} → ∀ ls C → B (`[_]_ {k} ls C))
       (∪* : ∀{x y} → B x → B y → B (x ∪ y))
       (·* : ∀{x y} → B x → B y → B (x · y))
       (ν* : ∀{x} → B x → B (ν x))
       where


  f : (x : State) → B x
  f x = Elim.f (λ x → isProp→isSet (BProp {x})) 0b* 1b* `[]* ∪* ·* ν*
               (λ x b bs →  toPathP (BProp (transp (λ i → B (ν-elim x i)) i0 (ν* bs)) b))
               (λ x y bx by bys → toPathP (BProp (transp (λ i → B (ν-∪ x y i)) i0 (ν* (∪* bx bys))) (∪* (ν* bx) by)))
               (λ x y bx by bys → toPathP (BProp (transp (λ i → B (ν-· x y i)) i0 (ν* (·* bx bys))) (·* (ν* bx) by)))
               (λ x y z bx by bz → toPathP (BProp (transp (λ i → B (assoc x y z i)) i0 (∪* bx (∪* by bz))) (∪* (∪* bx by) bz)))
               (λ x b → toPathP (BProp (transp (λ i → B (rid x i)) i0 (∪* b 0b*)) b))
               (λ x y bx by → toPathP (BProp (transp (λ i → B (comm x y i)) i0 (∪* bx by)) (∪* by bx)))
               (λ x b → toPathP (BProp (transp (λ i → B (idem x i)) i0 (∪* b b)) b))
               (λ x y z bx by bz → toPathP (BProp (transp (λ i → B (assoc· x y z i)) i0 (·* bx (·* by bz))) (·* (·* bx by) bz)))
               (λ x b → toPathP (BProp (transp (λ i → B (rid· x i)) i0 (·* b 1b*)) b))
               (λ x y bx by → toPathP (BProp (transp (λ i → B (comm· x y i)) i0 (·* bx by)) (·* by bx)))
               (λ x b → toPathP (BProp (transp (λ i → B (def∅· x i)) i0 (·* b 0b*)) 0b*))
               (λ x y z bx by bz → toPathP (BProp (transp (λ i → B (dist x y z i)) i0 (·* bx (∪* by bz))) (∪* (·* bx by) (·* bx bz))))
               x


module Rec {ℓ'} {B : Type ℓ'}
       (squash* : isSet B)
       (0b* : B)
       (1b* : B)
       (`[]* : ∀{k} → ∀ ls C → B)
       (∪* : B → B → B)
       (·*  : B → B → B)
       (ν* : B → B)
       (ν-elim* : ∀ b bs → ν* bs ≡ b)
       (ν-∪* : ∀ (bx by bys : B) → ν* (∪* bx bys) ≡ ∪* (ν* bx) by)
       (ν-·* : ∀ (bx by bys : B) → ν* (·* bx bys) ≡ ·* (ν* bx) by)
       (assoc* : (bx : B) → (by : B) → (bz : B) → (∪* bx (∪* by bz)) ≡ (∪* (∪* bx by) bz))
       (rid* : (b : B) → (∪* b 0b*) ≡ b)
       (comm* : (bx : B) → (by : B) → (∪* bx by) ≡ (∪* by bx))
       (idem* : (b : B) → (∪* b b) ≡ b)
       (assoc·* : (bx : B) → (by : B) → (bz : B) → (·* bx (·* by bz)) ≡ (·* (·* bx by) bz))
       (rid·* : (b : B) → (·* b 1b*) ≡ b)
       (comm·* : (bx : B) → (by : B) → (·* bx by) ≡ (·* by bx))
       (def∅·* : (bx : B) → (·* bx 0b*) ≡ 0b*)
       (dist* : (bx : B) → (by : B) → (bz : B) → (·* bx (∪* by bz)) ≡ (∪* (·* bx by) (·* bx bz)))

       where

  f : State → B
  f q = Elim.f (λ _ → squash*) 0b* 1b* (λ {k} ls C → `[]* {k} ls C) ∪* ·* ν* (λ _ → ν-elim*) (λ _ _ → ν-∪*) (λ _ _ → ν-·*) (λ _ _ _ → assoc*) (λ _ → rid*) (λ _ _ → comm*) (λ _ → idem*) (λ _ _ _ → assoc·*) (λ _ → rid·*) (λ _ _ → comm·*) (λ _ → def∅·*) (λ _ _ _ → dist*) q




