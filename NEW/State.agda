{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Vec as V
open import Cubical.Data.Fin hiding (_/_)
open import Cubical.Data.Bool hiding (isProp≤ ; _≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
import Cubical.Data.Nat.Order as O
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients renaming ([_] to ⟨_⟩ₛ) 
open import Cubical.Relation.Binary
open import Cubical.Core.Id hiding (_≡_)
import Cubical.Functions.Logic as L

open import State.Lemma

module State {ℓ} (C : (k : ℕ) → Type ℓ) where

infix 9 ν_
infixr 5 _∪_
infixr 7 _·_
infix 10 `_
infix 12 [_]_

record Particle (fv : ℕ) : Type ℓ where
  constructor [_]_
  field
    {k} : ℕ
    -- This is well-scoped by definition.
    secr : Vec (Fin fv) k
    c : C k

data SState : ℕ → Type ℓ where  
  0b      : ∀{fv} → SState fv
  1b      : ∀{fv} → SState fv
  `_       : ∀{fv} → Particle fv → SState fv
  _∪_     : ∀{fv} → (lq : SState fv) → (rq : SState fv) → SState fv
  _·_     : ∀{fv} → (lq : SState fv) → ( rq : SState fv) → SState fv
  ν_      : ∀{fv} → SState (suc fv) → SState fv

f-secr : ∀{fv} → (f : ∀{k} → Vec (Fin fv) k → Vec (Fin fv) k) → Particle fv → Particle fv
f-secr f ([ secr ] c) = [ f secr ] c

sucₛₛ : ∀{fv} → (q : SState fv) → ℕ → SState (suc fv)
sucₛₛ 0b n = 0b
sucₛₛ 1b n = 1b
sucₛₛ (` [ secr ] c) n = ` [ lsuc<?Fin secr n ] c 
sucₛₛ (lq ∪ rq) n = sucₛₛ lq n ∪ sucₛₛ rq n
sucₛₛ (lq · rq) n = sucₛₛ lq n · sucₛₛ rq n
sucₛₛ (ν q) n = ν sucₛₛ q (suc n)

swapₛₛ : ∀{fv} → Fin fv → Fin fv → (q : SState fv) → SState fv
swapₛₛ m n 0b = 0b
swapₛₛ m n 1b = 1b
swapₛₛ m n (` [ secr ] c) = ` [ lswapFin m n secr ] c 
swapₛₛ m n (lq ∪ rq) = swapₛₛ m n lq ∪ swapₛₛ m n rq
swapₛₛ m n (lq · rq) = swapₛₛ m n lq · swapₛₛ m n rq
swapₛₛ m n (ν q) = ν swapₛₛ (fsuc m) (fsuc n) q

id+ : ∀{fv} → (m : ℕ) → SState fv → SState (fv + suc m)
id+ m 0b = 0b
id+ m 1b = 0b
id+ {fv} m (` [ secr ] c) = ` [ V.map (inject≤ O.≤SumLeft) secr ] c
id+ m (q1 ∪ q2) = id+ m q1 ∪ id+ m q2
id+ m (q1 · q2) = id+ m q1 · id+ m q2
id+ m (ν q) = ν id+ m q

ν[_]_ : ∀{fv} → (n : ℕ) → SState (n + fv) → SState fv
ν[ zero ] q = q
ν[ suc x ] q = ν[ x ] (ν q)


data _R_ : ∀{fv} → SState fv → SState fv → Type ℓ where
  ⟨⟩-∪ : ∀{fv} → {lq1 rq1 lq2 rq2 : SState fv} → lq1 R lq2 → rq1 R rq2 → (lq1 ∪ rq1) R (lq2 ∪ rq2)
  ⟨⟩-· : ∀{fv} → {lq1 rq1 lq2 rq2 : SState fv} → lq1 R lq2 → rq1 R rq2 → (lq1 · rq1) R (lq2 · rq2)
  ⟨⟩-ν : ∀{fv} → {q1 q2 : SState (suc fv)} → q1 R q2 → (ν q1) R (ν q2)
  ν-swap` : ∀{fv} → (qs : SState (suc (suc fv))) → (ν ν (swapₛₛ 0 1 qs) ) R ( ν ν qs )
  ν-elim` : ∀{fv} → (qs : SState fv) → (ν sucₛₛ qs 0)  R qs
    -- We can add two ν from across _∪_ because even though they represent different secrets
    -- it is impossible for them to interact with each other, they represent different "time lines."
  ν-∪`    : ∀{fv} → (qs zs : SState (suc fv)) → ( ν (zs ∪ qs) ) R ( ν zs ∪ ν qs )
  ν-·`    : ∀{fv} → (qs : SState fv) → (zs : SState (suc fv)) → ( ν (zs · sucₛₛ qs 0) ) R ( ν zs · qs )
  assoc   : ∀{fv} → (x y z : SState fv) → ( x ∪ (y ∪ z) ) R ( (x ∪ y) ∪ z )
  rid     : ∀{fv} → (x : SState fv) → ( x ∪ 0b ) R ( x )
  comm    : ∀{fv} → (x y : SState fv) → ( x ∪ y ) R ( y ∪ x )
-- Equal terms here mean that we have equal state, but maybe we can have different actors (locationwise),
-- This also means that actors that the secret of ν does not play a role in the equality here.
-- In other words, as long as the structure is the same, it is the same state.
  idem    : ∀{fv} → (x : SState fv) → ( x ∪ x ) R ( x )
  assoc·  : ∀{fv} → (x y z : SState fv) → ( x · (y · z) ) R ( (x · y) · z )
  rid·    : ∀{fv} → (x : SState fv) → ( x · 1b ) R ( x )
  comm·   : ∀{fv} → (x y : SState fv) → ( x · y ) R ( y · x )
  def∅·   : ∀{fv} → (x : SState fv) → ( x · 0b ) R ( 0b )
  dist    : ∀{fv} → (x y z : SState fv) → ( x · (y ∪ z) ) R ( (x · y) ∪ (x · z) )
  refl`    : ∀{fv} → (x : SState fv) → x R x
  sym`    : ∀{fv} → (x y : SState fv) → x R y → y R x
  trans`  : ∀{fv} → (x y z : SState fv) → x R y → y R z → x R z
  squash₁ : ∀{fv} → (x y : SState fv) → isProp (x R y)
  



State : ∀ n → Type ℓ
State n = SState n / _R_

open BinaryRelation

RisPropValued : ∀{fv} → isPropValued _R_
RisPropValued {fv} a b = squash₁ {fv} a b

RisEquivRel : ∀{fv} → isEquivRel _R_
isEquivRel.reflexive (RisEquivRel {fv}) = refl` {fv}
isEquivRel.symmetric RisEquivRel = sym`
isEquivRel.transitive RisEquivRel = trans`
