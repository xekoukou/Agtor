{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive as O
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Core.Id hiding (_≡_)
import Cubical.Functions.Logic as L

open import State.Lemma

module State {ℓ} (C : (k : ℕ) → Type ℓ) where

infix 9 ν_
infixr 5 _∪_
infixr 7 _·_
infix 10 `_
infix 12 [_]_

record Particle : Type ℓ where
  constructor [_]_
  field
    {k} : ℕ
    secr : Vec ℕ k
    c : C k

data SState : Type ℓ where  
  0b      : SState
  1b      : SState
  `_       : Particle → SState
  _∪_     : (lq : SState) → (rq : SState) → SState 
  _·_     : (lq : SState) → ( rq : SState) → SState
  ν_      : SState → SState

mapₛₛ : (f : Particle → Particle) → (q : SState) → SState
mapₛₛ f 0b = 0b
mapₛₛ f 1b = 1b
mapₛₛ f (` x) = ` f x
mapₛₛ f (lq ∪ rq) = mapₛₛ f lq ∪ mapₛₛ f rq 
mapₛₛ f (lq · rq) = mapₛₛ f lq · mapₛₛ f rq 
mapₛₛ f (ν q) = ν mapₛₛ f q

f-secr : (f : ∀{k} → Vec ℕ k → Vec ℕ k) → Particle → Particle
f-secr f ([ secr ] c) = [ f secr ] c

sucₛₛ : (q : SState) → ℕ → SState
sucₛₛ 0b n = 0b
sucₛₛ 1b n = 1b
sucₛₛ (` [ secr ] c) n = ` [ lsuc<? secr n ] c 
sucₛₛ (lq ∪ rq) n = sucₛₛ lq n ∪ sucₛₛ rq n
sucₛₛ (lq · rq) n = sucₛₛ lq n · sucₛₛ rq n
sucₛₛ (ν q) n = ν sucₛₛ q (suc n)

swapₛₛ : ℕ → ℕ → (q : SState) → SState
swapₛₛ m n 0b = 0b
swapₛₛ m n 1b = 1b
swapₛₛ m n (` [ secr ] c) = ` [ lswap m n secr ] c 
swapₛₛ m n (lq ∪ rq) = swapₛₛ m n lq ∪ swapₛₛ m n rq
swapₛₛ m n (lq · rq) = swapₛₛ m n lq · swapₛₛ m n rq
swapₛₛ m n (ν q) = ν swapₛₛ (suc m) (suc n) q

ν[_]_ : ℕ → SState → SState
ν[ zero ] q = q
ν[ suc x ] q = ν ν[ x ] q




data State : Type ℓ where
  ⟨_⟩ₛ : SState → State
  ⟨⟩-∪ : ∀{lq1 rq1 lq2 rq2} → ⟨ lq1 ⟩ₛ ≡ ⟨ lq2 ⟩ₛ → ⟨ rq1 ⟩ₛ ≡ ⟨ rq2 ⟩ₛ → ⟨ lq1 ∪ rq1 ⟩ₛ ≡ ⟨ lq2 ∪ rq2 ⟩ₛ
  ⟨⟩-· : ∀{lq1 rq1 lq2 rq2} → ⟨ lq1 ⟩ₛ ≡ ⟨ lq2 ⟩ₛ → ⟨ rq1 ⟩ₛ ≡ ⟨ rq2 ⟩ₛ → ⟨ lq1 · rq1 ⟩ₛ ≡ ⟨ lq2 · rq2 ⟩ₛ
  ⟨⟩-ν : ∀{q1 q2} → ⟨ q1 ⟩ₛ ≡ ⟨ q2 ⟩ₛ → ⟨ ν q1 ⟩ₛ ≡ ⟨ ν q2 ⟩ₛ
  ν-swap` : ∀ qs → ⟨ ν ν (swapₛₛ 0 1 qs) ⟩ₛ ≡ ⟨ ν ν qs ⟩ₛ
  ν-elim` : ∀ qs → ⟨ ν sucₛₛ qs 0 ⟩ₛ ≡ ⟨ qs ⟩ₛ
  ν-∪`    : ∀ qs zs → ⟨ ν (zs ∪ sucₛₛ qs 0) ⟩ₛ ≡ ⟨ ν zs ∪ qs ⟩ₛ
  ν-·`    : ∀ qs zs → ⟨ ν (zs · sucₛₛ qs 0) ⟩ₛ ≡ ⟨ ν zs · qs ⟩ₛ
  assoc   : (x y z : SState) → ⟨ x ∪ (y ∪ z) ⟩ₛ ≡ ⟨ (x ∪ y) ∪ z ⟩ₛ
  rid     : (x : SState) → ⟨ x ∪ 0b ⟩ₛ ≡ ⟨ x ⟩ₛ
  comm    : (x y : SState ) → ⟨ x ∪ y ⟩ₛ ≡ ⟨ y ∪ x ⟩ₛ
-- -- -- Equal terms here mean that we have equal state, but maybe we can have different actors (locationwise),
-- -- -- This also means that actors that the secret of ν does not play a role in the equality here.
-- -- -- In other words, as long as the structure is the same, it is the same state.
  idem    : (x : SState) → ⟨ x ∪ x ⟩ₛ ≡ ⟨ x ⟩ₛ
  assoc·  : (x y z : SState) → ⟨ x · (y · z) ⟩ₛ ≡ ⟨ (x · y) · z ⟩ₛ
  rid·    : (x : SState) → ⟨ x · 1b ⟩ₛ ≡ ⟨ x ⟩ₛ
  comm·   : (x y : SState) → ⟨ x · y ⟩ₛ ≡ ⟨ y · x ⟩ₛ
  def∅·   : (x : SState) → ⟨ x · 0b ⟩ₛ ≡ ⟨ 0b ⟩ₛ
  dist    : (x y z : SState) → ⟨ x · (y ∪ z) ⟩ₛ ≡ ⟨ (x · y) ∪ (x · z) ⟩ₛ
  squash  : isSet (State)

module Elim {ℓ'} {B : State → Type ℓ'}
       (squash* : ∀ x → isSet (B x))
       (0b* : B ⟨ 0b ⟩ₛ )
       (1b* : B ⟨ 1b ⟩ₛ )
       (`[]* : ∀{k} → ∀ ls C → B ⟨ ` [_]_ {k} ls C ⟩ₛ)
       (∪* : ∀{x y} → B ⟨ x ⟩ₛ → B ⟨ y ⟩ₛ → B ⟨ x ∪ y ⟩ₛ)
       (·* : ∀{x y} → B ⟨ x ⟩ₛ → B ⟨ y ⟩ₛ → B ⟨ x · y ⟩ₛ)
       (ν* : ∀{x} → B ⟨ x ⟩ₛ → B ⟨ ν x ⟩ₛ)
       (⟨⟩-∪* : ∀{lq1 rq1 lq2 rq2} → (eq1 : ⟨ lq1 ⟩ₛ ≡ ⟨ lq2 ⟩ₛ) → (eq2 : ⟨ rq1 ⟩ₛ ≡ ⟨ rq2 ⟩ₛ )
               → (blq1 : B ⟨ lq1 ⟩ₛ) → (brq1 : B ⟨ rq1 ⟩ₛ) → (blq2 : B ⟨ lq2 ⟩ₛ) → (brq2 : B ⟨ rq2 ⟩ₛ)
               → PathP (λ i → B (⟨⟩-∪ eq1 eq2 i)) (∪* blq1 brq1) (∪* blq2 brq2))
       (⟨⟩-·* : ∀{lq1 rq1 lq2 rq2} → (eq1 : ⟨ lq1 ⟩ₛ ≡ ⟨ lq2 ⟩ₛ) → (eq2 : ⟨ rq1 ⟩ₛ ≡ ⟨ rq2 ⟩ₛ )
               → (blq1 : B ⟨ lq1 ⟩ₛ) → (brq1 : B ⟨ rq1 ⟩ₛ) → (blq2 : B ⟨ lq2 ⟩ₛ) → (brq2 : B ⟨ rq2 ⟩ₛ)
               → PathP (λ i → B (⟨⟩-· eq1 eq2 i)) (·* blq1 brq1) (·* blq2 brq2))
       (⟨⟩-ν* : ∀{q1 q2} → (eq : ⟨ q1 ⟩ₛ ≡ ⟨ q2 ⟩ₛ)
               → (bq1 : B ⟨ q1 ⟩ₛ) → (bq2 : B ⟨ q2 ⟩ₛ)
               → PathP (λ i → B (⟨⟩-ν eq i)) (ν* bq1) (ν* bq2))
       (ν-swap`* : ∀{qs} → (b : B ⟨ qs ⟩ₛ) → (bs : B ⟨ swapₛₛ 0 1 qs ⟩ₛ ) → PathP (λ i → B (ν-swap` qs i)) (ν* (ν* bs)) (ν* (ν* b)))
       (ν-elim`* : ∀{qs} → (b : B ⟨ qs ⟩ₛ) → (bs : B ⟨ sucₛₛ qs 0 ⟩ₛ ) → PathP (λ i → B (ν-elim` qs i)) (ν* bs) b)
       (ν-∪`* : ∀{qs zs} → (bq : B ⟨ qs ⟩ₛ ) → (bqs : B ⟨ sucₛₛ qs 0 ⟩ₛ ) → (bz : B ⟨ zs ⟩ₛ) → PathP (λ i → B (ν-∪` qs zs i)) (ν* (∪* bz bqs)) (∪* (ν* bz) bq))
       (ν-·`* : ∀{qs zs} → (bq : B ⟨ qs ⟩ₛ ) → (bqs : B ⟨ sucₛₛ qs 0 ⟩ₛ ) → (bz : B ⟨ zs ⟩ₛ) → PathP (λ i → B (ν-·` qs zs i)) (ν* (·* bz bqs)) (·* (ν* bz) bq))
       (assoc* : ∀{x y z} → (bx : B ⟨ x ⟩ₛ ) → (by : B ⟨ y ⟩ₛ ) → (bz : B ⟨ z ⟩ₛ ) → PathP (λ i → B (assoc x y z i)) (∪* bx (∪* by bz)) (∪* (∪* bx by) bz))
       (rid* : ∀{x} → (b : B ⟨ x ⟩ₛ ) → PathP (λ i → B (rid x i)) (∪* b 0b*) b)
       (comm* : ∀{x y} → (bx : B ⟨ x ⟩ₛ ) → (by : B ⟨ y ⟩ₛ ) → PathP (λ i → B (comm (x) (y) i)) (∪* bx by) (∪* by bx))
       (idem* : ∀{x} → (b : B ⟨ x ⟩ₛ ) → PathP (λ i → B (idem x i)) (∪* b b) b)
       (assoc·* : ∀{x y z} → (bx : B ⟨ x ⟩ₛ ) → (by : B ⟨ y ⟩ₛ ) → (bz : B ⟨ z ⟩ₛ ) → PathP (λ i → B (assoc· x y z i)) (·* bx (·* by bz)) (·* (·* bx by) bz))
       (rid·* : ∀{x} → (b : B ⟨ x ⟩ₛ ) → PathP (λ i → B (rid· x i)) (·* b 1b*) b)
       (comm·* : ∀{x y} → (bx : B ⟨ x ⟩ₛ ) → (by : B ⟨ y ⟩ₛ ) → PathP (λ i → B (comm· x y i)) (·* bx by) (·* by bx))
       (def∅·* : ∀{x} → (bx : B ⟨ x ⟩ₛ ) → PathP (λ i → B (def∅· x i)) (·* bx 0b*) 0b*)
       (dist* : ∀{x y z} → (bx : B ⟨ x ⟩ₛ ) → (by : B ⟨ y ⟩ₛ ) → (bz : B ⟨ z ⟩ₛ ) → PathP (λ i → B (dist x y z i)) (·* bx (∪* by bz)) (∪* (·* bx by) (·* bx bz)))
       
       where

  f` : (x : SState) → B ⟨ x ⟩ₛ
  f` 0b = 0b*
  f` 1b = 1b*
  f` (` [ ls ] C)  = `[]* ls C
  f` (x ∪ y) = ∪* (f` x) (f` y)
  f` (x · y) = ·* (f` x) (f` y)
  f` (ν q) = ν* (f` q)
  
  f : (x : State) → B x
  f ⟨ x ⟩ₛ = f` x
  f (squash a b p1 p2 i j) = isOfHLevel→isOfHLevelDep 2 squash*  (f a) (f b) (cong f p1) (cong f p2) (squash a b p1 p2) i j
  f (assoc x y z i) = assoc* (f` x) (f` y ) (f` z) i
  f (rid x i) = rid* (f` x) i
  f (comm x y i) = comm* (f` x ) (f` y  ) i
  f (idem x i) = idem* (f` x ) i
  f (assoc· x y z i) = assoc·* (f` x ) (f` y) (f`  z  ) i
  f (rid· x i) = rid·* (f` x ) i
  f (comm· x y i) = comm·* (f` x ) (f` y) i
  f (def∅· x i) = def∅·* (f` x ) i
  f (dist x y z i) = dist* (f` x ) (f` y) (f` z) i
  f (ν-swap` q i) = ν-swap`* (f` q) (f` (swapₛₛ 0 1 q)) i
  f (ν-elim` q i) = ν-elim`* (f` q) (f` (sucₛₛ q 0)) i
  f (ν-∪` q z i) = ν-∪`* (f` q) (f` (sucₛₛ q 0)) (f` z) i
  f (ν-·` q z i) = ν-·`* (f` q) (f` (sucₛₛ q 0)) (f` z) i
  f (⟨⟩-∪ eq1 eq2 i) = ⟨⟩-∪* eq1 eq2 (f` _) (f` _) (f` _) (f` _) i
  f (⟨⟩-· eq1 eq2 i) = ⟨⟩-·* eq1 eq2 (f` _) (f` _) (f` _) (f` _) i
  f (⟨⟩-ν eq1 i) = ⟨⟩-ν* eq1 (f` _) (f` _) i


module ElimProp {ℓ'} {B : State → Type ℓ'}
       (BProp : ∀{x} → isProp (B x))
       (0b* : B ⟨ 0b ⟩ₛ )
       (1b* : B ⟨ 1b ⟩ₛ )
       (`[]* : ∀{k} → ∀ ls C → B ⟨ ` [_]_ {k} ls C ⟩ₛ)
       (∪* : ∀{x y} → B ⟨ x ⟩ₛ → B ⟨ y ⟩ₛ → B ⟨ x ∪ y ⟩ₛ)
       (·* : ∀{x y} → B ⟨ x ⟩ₛ → B ⟨ y ⟩ₛ → B ⟨ x · y ⟩ₛ)
       (ν* : ∀{x} → B ⟨ x ⟩ₛ → B ⟨ ν x ⟩ₛ)
       where


  f : (x : State) → B x
  f x = Elim.f (λ x → isProp→isSet (BProp {x})) 0b* 1b* `[]* ∪* ·* ν*
               (λ eq1 eq2 blq1 brq1 blq2 brq2 i → toPathP {A = λ i → B (⟨⟩-∪ eq1 eq2 i)} {x = ∪* blq1 brq1} (BProp (transp (λ i → B (⟨⟩-∪ eq1 eq2 i)) i0 (∪* blq1 brq1)) (∪* blq2 brq2)) i)
               (λ eq1 eq2 blq1 brq1 blq2 brq2 i → toPathP {A = λ i → B (⟨⟩-· eq1 eq2 i)} {x = ·* blq1 brq1} (BProp (transp (λ i → B (⟨⟩-· eq1 eq2 i)) i0 (·* blq1 brq1)) (·* blq2 brq2)) i)
               (λ eq1 bq1 bq2 i → toPathP {A = λ i → B (⟨⟩-ν eq1 i)} {x = ν* bq1} (BProp (transp (λ i → B (⟨⟩-ν eq1 i)) i0 (ν* bq1)) (ν* bq2)) i)
               (λ {q} b bs i → toPathP {A = λ i → B (ν-swap` q i)} {x = ν* (ν* bs)} (BProp (transp (λ i → B (ν-swap` q i)) i0 (ν* (ν* bs))) (ν* (ν* b))) i)
               (λ {q} b bs i → toPathP {A = λ i → B (ν-elim` q i)} {x = ν* bs} (BProp (transp (λ i → B (ν-elim` q i)) i0 (ν* bs)) b) i)
               (λ {q} {z} bq bqs bz i → toPathP {A = λ i → B (ν-∪` q z i)} {x = ν* (∪* bz bqs)} (BProp (transp (λ i → B (ν-∪` q z i)) i0 (ν* (∪* bz bqs))) (∪* (ν* bz) bq)) i)
               (λ {q} {z} bq bqs bz i → toPathP {A = λ i → B (ν-·` q z i)} {x = ν* (·* bz bqs)} (BProp (transp (λ i → B (ν-·` q z i)) i0 (ν* (·* bz bqs))) (·* (ν* bz) bq)) i)
               (λ {x} {y} {z} bx by bz → toPathP (BProp (transp (λ i → B (assoc x y z i)) i0 (∪* bx (∪* by bz))) (∪* (∪* bx by) bz)))
               (λ {x} b → toPathP (BProp (transp (λ i → B (rid x i)) i0 (∪* b 0b*)) b))
               (λ {x} {y} bx by → toPathP (BProp (transp (λ i → B (comm x y i)) i0 (∪* bx by)) (∪* by bx)))
               (λ {x} b → toPathP (BProp (transp (λ i → B (idem x i)) i0 (∪* b b)) b))
               (λ {x} {y} {z} bx by bz → toPathP (BProp (transp (λ i → B (assoc· x y z i)) i0 (·* bx (·* by bz))) (·* (·* bx by) bz)))
               (λ {x} b → toPathP (BProp (transp (λ i → B (rid· x i)) i0 (·* b 1b*)) b))
               (λ {x} {y} bx by → toPathP (BProp (transp (λ i → B (comm· x y i)) i0 (·* bx by)) (·* by bx)))
               (λ {x} b → toPathP (BProp (transp (λ i → B (def∅· x i)) i0 (·* b 0b*)) 0b*))
               (λ {x} {y} {z} bx by bz → toPathP (BProp (transp (λ i → B (dist x y z i)) i0 (·* bx (∪* by bz))) (∪* (·* bx by) (·* bx bz))))
               x


module Rec {ℓ'} {B : Type ℓ'}
       (squash* : isSet B)
       (0b* : B)
       (1b* : B)
       (`[]* : ∀{k} → ∀ ls c → B)
       (∪* : B → B → B)
       (·*  : B → B → B)
       (ν* : B → B)
       (⟨⟩-∪* : ∀ lbq1 rbq1 lbq2 rbq2 → ∪* lbq1 rbq1 ≡ ∪* lbq2 rbq2)
       (⟨⟩-·* : ∀ lbq1 rbq1 lbq2 rbq2 → ·* lbq1 rbq1 ≡ ·* lbq2 rbq2)
       (⟨⟩-ν* : ∀ bq1 bq2 → ν* bq1 ≡ ν* bq2)
       (ν-swap`* : (b bs : B) → ν* (ν* bs) ≡ (ν* (ν* b)))
       (ν-elim`* : (b bs : B) → ν* bs ≡ b)
       (ν-∪`* : (by bys bx : B) → ν* (∪* bx bys) ≡ ∪* (ν* bx) by)
       (ν-·`* : (by bys bx : B) → ν* (·* bx bys) ≡ ·* (ν* bx) by)
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
  f q = Elim.f (λ _ → squash*) 0b* 1b* (λ {k} ls C → `[]* {k} ls C) ∪* ·* ν*
               (λ eq1 eq2 → ⟨⟩-∪*) (λ eq1 eq2 → ⟨⟩-·*) (λ eq₁ → ⟨⟩-ν*) ν-swap`* ν-elim`* ν-∪`* ν-·`* assoc* rid* comm* idem* assoc·* rid·* comm·* def∅·* dist* q


All< : ∀{e} → Vec ℕ e → ℕ → Type
All< [] k = Unit
All< (x ∷ xs) k = (x < k) × All< xs k


data WellScopedₛₛ : SState → ℕ → Type ℓ where
  ws-0b : ∀{k} → WellScopedₛₛ 0b k
  ws-1b : ∀{k} → WellScopedₛₛ 1b k
  ws-`  : ∀{k n secr c} → All< secr k → WellScopedₛₛ (` ([_]_ {n} secr c)) k
  ws-∪  : ∀{k lq rq} → WellScopedₛₛ lq k → WellScopedₛₛ rq k → WellScopedₛₛ (lq ∪ rq) k
  ws-·  : ∀{k lq rq} → WellScopedₛₛ lq k → WellScopedₛₛ rq k → WellScopedₛₛ (lq · rq) k
  ws-ν  : ∀{k q} → WellScopedₛₛ q (suc k) → WellScopedₛₛ (ν q) k






-- -- -- -- -- module _ where


-- -- -- -- --   All : ∀{e} → Vec ℕ e → ℕ → Type
-- -- -- -- --   All [] k = Unit
-- -- -- -- --   All (x ∷ xs) k = (x < k) × All xs k

-- -- -- -- --   WellScoped : SState → ℕ → Type
-- -- -- -- --   WellScoped ⟨ 0bₛ ⟩ₛ k = Unit
-- -- -- -- --   WellScoped ⟨ 1bₛ ⟩ₛ k = Unit
-- -- -- -- --   WellScoped ⟨ `[ ls ]ₛ c ⟩ₛ k = All ls k
-- -- -- -- --   WellScoped ⟨ s₁ ∪ₛ s₂ ⟩ₛ k = WellScoped ⟨ s₁ ⟩ₛ k × WellScoped ⟨ s₂ ⟩ₛ k
-- -- -- -- --   WellScoped ⟨ s₁ ·ₛ s₂ ⟩ₛ k = WellScoped ⟨ s₁ ⟩ₛ k × WellScoped ⟨ s₂ ⟩ₛ k
-- -- -- -- --   WellScoped ⟨ νₛ s₁ ⟩ₛ k = WellScoped ⟨ s₁ ⟩ₛ (suc k)

-- -- -- -- --   All` : ∀{e} → Vec ℕ e → ℕ → hProp ℓ-zero
-- -- -- -- --   All` [] k = Unit , isPropUnit
-- -- -- -- --   All` (x ∷ xs) k = (x < k) × fst (All` xs k) , isProp× (O.isProp≤ {suc x} {k}) (snd (All` xs k))


-- -- -- -- --   WellScoped` : State → ℕ → hProp ℓ-zero
-- -- -- -- --   {-# TERMINATING #-}
-- -- -- -- --   -- This is terminating because s can only increase a finite ammount because of ν in State.
-- -- -- -- --   WellScoped`-suc : ∀{s k} → ∀ n → WellScoped` (sucₛ n s) (n + suc k) ≡ WellScoped` s k




-- -- -- -- --   WellScoped` 0b k = Unit , isPropUnit
-- -- -- -- --   WellScoped` 1b k = Unit , isPropUnit
-- -- -- -- --   WellScoped` (`[ ls ] x) k = All` ls k
-- -- -- -- --   WellScoped` (s₁ ∪ s₂) k = ⟨ WellScoped` s₁ k ⟩  × ⟨ WellScoped` s₂ k ⟩ , isProp× (snd (WellScoped` s₁ k)) (snd (WellScoped` s₂ k))
-- -- -- -- --   WellScoped` (s₁ · s₂) k = ⟨ WellScoped` s₁ k ⟩  × ⟨ WellScoped` s₂ k ⟩ , isProp× (snd (WellScoped` s₁ k)) (snd (WellScoped` s₂ k))
-- -- -- -- --   WellScoped` (ν s₁) k = ⟨ WellScoped` s₁ (suc k) ⟩ , snd (WellScoped` s₁ (suc k))
-- -- -- -- --   WellScoped` (ν-elim s₁ i) k = WellScoped`-suc {s₁} {k} 0 i
-- -- -- -- --   WellScoped` (ν-∪ s₁ s₂ i) k = {!!}
-- -- -- -- --   WellScoped` (ν-· s₁ s₂ i) k = {!!}
-- -- -- -- --   WellScoped` (squash s₁ s₂ x y i i₁) k = {!!}
-- -- -- -- --   WellScoped` (assoc s₁ s₂ s₃ i) k = {!!}
-- -- -- -- --   WellScoped` (rid s₁ i) k = {!!}
-- -- -- -- --   WellScoped` (comm s₁ s₂ i) k = {!!}
-- -- -- -- --   WellScoped` (idem s₁ i) k = {!!}
-- -- -- -- --   WellScoped` (assoc· s₁ s₂ s₃ i) k = {!!}
-- -- -- -- --   WellScoped` (rid· s₁ i) k = {!!}
-- -- -- -- --   WellScoped` (comm· s₁ s₂ i) k = {!!}
-- -- -- -- --   WellScoped` (def∅· s₁ i) k = {!!}
-- -- -- -- --   WellScoped` (dist s₁ s₂ s₃ i) k = {!!}


-- -- -- -- --   WellScoped`-suc {s} {k} n
-- -- -- -- --     = L.⇔toPath {P = WellScoped` (sucₛ n s) (n + suc k)} {Q = WellScoped` s k} (P→Q s n) (Q→P s n) where
-- -- -- -- --       P→Q : ∀ s n → ⟨ WellScoped` (sucₛ n s) (n + suc k) ⟩ → ⟨ WellScoped` s k ⟩
-- -- -- -- --       P→Q s n = ElimProp.f (λ {x} → isPropΠ (snd {!WellScoped` {x} {k}!})) {!!} {!!} {!!} {!!} {!!} {!!} s
-- -- -- -- --       Q→P : ∀ s n → ⟨ WellScoped` s k ⟩ → ⟨ WellScoped` (sucₛ n s) (n + suc k) ⟩
-- -- -- -- --       Q→P = {!!}
  


-- -- -- -- --   -- All` : ∀{e} → Vec ℕ e → ℕ → Bool
-- -- -- -- --   -- All` [] k = true
-- -- -- -- --   -- All` (x ∷ xs) k = x <? k and All` xs k

-- -- -- -- --   -- WellScoped` : State → ℕ → Bool
-- -- -- -- --   -- WellScoped` 0b k = true
-- -- -- -- --   -- WellScoped` 1b k = true
-- -- -- -- --   -- WellScoped` (`[ ls ] x) k = All ls k
-- -- -- -- --   -- WellScoped` (s₁ ∪ s₂) k = WellScoped` s₁ k × WellScoped` s₂ k
-- -- -- -- --   -- WellScoped` (s₁ · s₂) k = WellScoped` s₁ k × WellScoped` s₂ k
-- -- -- -- --   -- WellScoped` (ν s₁) k = WellScoped` s₁ (suc k)
-- -- -- -- --   -- WellScoped` (ν-elim s₁ i) k = {!!}
-- -- -- -- --   -- WellScoped` (ν-∪ s₁ s₂ i) k = {!!}
-- -- -- -- --   -- WellScoped` (ν-· s₁ s₂ i) k = {!!}
-- -- -- -- --   -- WellScoped` (squash s₁ s₂ x y i i₁) k = {!!}
-- -- -- -- --   -- WellScoped` (assoc s₁ s₂ s₃ i) k = {!!}
-- -- -- -- --   -- WellScoped` (rid s₁ i) k = {!!}
-- -- -- -- --   -- WellScoped` (comm s₁ s₂ i) k = {!!}
-- -- -- -- --   -- WellScoped` (idem s₁ i) k = {!!}
-- -- -- -- --   -- WellScoped` (assoc· s₁ s₂ s₃ i) k = {!!}
-- -- -- -- --   -- WellScoped` (rid· s₁ i) k = {!!}
-- -- -- -- --   -- WellScoped` (comm· s₁ s₂ i) k = {!!}
-- -- -- -- --   -- WellScoped` (def∅· s₁ i) k = {!!}
-- -- -- -- --   -- WellScoped` (dist s₁ s₂ s₃ i) k = {!!}

-- -- -- -- -- plus : ℕ → ℕ → ℕ
-- -- -- -- -- plus zero y = zero
-- -- -- -- -- plus (suc x) y = plus x (suc y)