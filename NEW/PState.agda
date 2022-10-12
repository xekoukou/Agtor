{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as M
open import Cubical.Data.List
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import SemiRing

module PState where

_>>=_ : ∀{ℓ1 ℓ2 D A} → Maybe {ℓ1} D → (D → Maybe A) → Maybe {ℓ2} A
nothing >>= f = nothing
just x >>= f = f x

_+|_|+ₘ_ : ∀{ℓ1 D} → Maybe {ℓ1} D → (D → D → D) → Maybe {ℓ1} D → Maybe D
nothing +| f |+ₘ y = y
just x +| f |+ₘ nothing = just x
just x +| f |+ₘ just y = just (f x y)



lsuc : List ℕ → List ℕ
lsuc [] = []
lsuc (x ∷ xs) = suc x ∷ xs

lpred : List ℕ → List ℕ
lpred [] = []
lpred (zero ∷ xs) = xs
lpred (suc x ∷ xs) = x ∷ xs

g : List ℕ → List ℕ → List ℕ
g [] ys = ys
g xs [] = xs
g (zero ∷ xs) (zero ∷ ys) = zero ∷ g xs ys
g (zero ∷ xs) (suc y ∷ ys) = zero ∷ g xs (y ∷ ys)
g (suc x ∷ xs) (zero ∷ ys) = zero ∷ g (x ∷ xs) ys
g (suc x ∷ xs) (suc y ∷ ys) = lsuc (g (x ∷ xs) (y ∷ ys))



private
  variable
    ℓ : Level

infixr 5 _∪_
infixr 7 _·_
infixr 10 `_

module _ (C : (List ℕ) → Type ℓ) (oo : ∀{l1} → C l1 → ∀ l2 → length l1 ≡ length l2 → C l2) where

  mutual
  
    data QState : List ℕ → Type ℓ where  
      0b      : QState []
      1b      : QState
      `_      : ∀{l} → C l → QState
      _∪_     : QState → QState → QState  
      _·_     : QState → QState → QState
      ν_      : QState → QState
      ν-elim  : ∀{q} → DDD q → ν q ≡ {!!}
      squash  : isSet (QState)
      assoc   : {x y z : QState} → (x ∪ (y ∪ z)) ≡ ((x ∪ y) ∪ z)
      rid     : {x : QState} → x ∪ 0b ≡ x
      comm    : {x y : QState} → x ∪ y ≡ y ∪ x
-- Equal terms here mean that we have equal state, but maybe we can have different actors (locationwise),
-- This also means that actors that the secret of ν does not play a role in the equality here.
-- In other words, as long as the structure is the same, it is the same state.
      idem    : {x : QState} → x ∪ x ≡ x
      assoc·   : {x y z : QState} → x · (y · z) ≡ (x · y) · z
      rid·     : {x : QState} → x · 1b ≡ x
      comm·    : {x y : QState} → x · y ≡ y · x
      def∅·   : {x : QState} → x · 0b ≡ 0b
      dist    : {x y z : QState} → x · (y ∪ z) ≡ (x · y) ∪ (x · z)

    DD : QState → Type
    DD q = (ee q ≡ []) ⊎ (∃[ n ∈ ℕ ] ∃[ xs ∈ List ℕ ] (ee q) ≡ suc n ∷ xs)

    DDD : QState → Type ℓ
    DDD q = E q nothing ⊎ (E q (just []) ⊎ Σ ℕ λ n → Σ (List ℕ) λ xs → E q (just (suc n ∷ xs)))

    data E : QState → Maybe (List ℕ) → Type ℓ where
      e0b : E 0b nothing
      e1b : E 1b (just [])
      e` : ∀ {l x} → E (`_ {l} x) (just l)
      e∪ : ∀{l1 l2} → ∀ q1 q2 → E q1 l1 → E q2 l2 → E (q1 ∪ q2) (l1 +| g |+ₘ l2)
      e· : ∀{l1 l2} → ∀ q1 q2 → E q1 l1 → E q2 l2 → E (q1 · q2) (l1 >>= λ l1 → l2 >>= λ l2 → just (g l1 l2))
      eν : ∀{l} → ∀ q → E q l → E (ν q) (l >>= λ l → just (lpred l))

    e : (q : QState) → Σ (Maybe (List ℕ)) (λ m → (E q m))
    e 0b = nothing , e0b
    e 1b = just [] , e1b
    e (`_ {l} x) = just l , e`
    e (q1 ∪ q2) = fst (e q1) +| g |+ₘ fst (e q2) , e∪ q1 q2 (snd (e q1)) (snd (e q2))
    e (q1 · q2) = ((fst (e q1)) >>= λ l1 → (fst (e q2)) >>= λ l2 → just (g l1 l2)) , e· q1 q2 (snd (e q1)) (snd (e q2))
    e (ν q) = (fst (e q) >>= λ l → just (lpred l)) , eν q (snd (e q))
    e (squash a b p1 p2 i j) = {!!} -- isOfHLevel→isOfHLevelDep 2 (λ _ → isOfHLevelMaybe 0 (isOfHLevelList 0 isSetℕ)) (e a) (e b) (cong e p1) (cong e p2) (squash a b p1 p2) i j
    e (assoc i) = {!!}
    e (rid i) = {!!}
    e (comm i) = {!!}
    e (idem i) = {!!}
    e (assoc· i) = {!!}
    e (rid· i) = {!!}
    e (comm· i) = {!!}
    e (def∅· i) = {!!}
    e (dist i) = {!!}
  
    ee : QState → List ℕ
    ee q = M.rec [] (λ x → x) {!!} -- (e q)
  
    lpredq : (q : QState) → DDD q → QState
    lpredq 0b e = 0b
    lpredq 1b e = 1b
    lpredq (` x) (inl e) = {!!}
    lpredq (` x) (inr e) = {!!}
    lpredq (q ∪ q₁) e = {!!}
    lpredq (q · q₁) e = {!!}
    lpredq (ν q) e = {!!}
    lpredq (ν-elim x i) e = {!!}
    lpredq (squash q q₁ x y i i₁) e = {!!}
    lpredq (assoc i) e = {!!}
    lpredq (rid i) e = {!!}
    lpredq (comm i) e = {!!}
    lpredq (idem i) e = {!!}
    lpredq (assoc· i) e = {!!}
    lpredq (rid· i) e = {!!}
    lpredq (comm· i) e = {!!}
    lpredq (def∅· i) e = {!!}
    lpredq (dist i) e = {!!}
