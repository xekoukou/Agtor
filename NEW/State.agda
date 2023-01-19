{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Bool hiding (isProp≤ ; _≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive as O
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


data _R_ : SState → SState → Type ℓ where
  ⟨⟩-∪ : ∀{lq1 rq1 lq2 rq2} → lq1 R lq2 → rq1 R rq2 → (lq1 ∪ rq1) R (lq2 ∪ rq2)
  ⟨⟩-· : ∀{lq1 rq1 lq2 rq2} → lq1 R lq2 → rq1 R rq2 → (lq1 · rq1) R (lq2 · rq2)
  ⟨⟩-ν : ∀{q1 q2} → q1 R q2 → (ν q1) R (ν q2)
  ν-swap` : ∀ qs → (ν ν (swapₛₛ 0 1 qs) ) R ( ν ν qs )
  ν-elim` : ∀ qs → ( ν sucₛₛ qs 0 ) R ( qs )
    -- I need to change this to let ν to be split on _∪_
    -- because during reduction, we will need this.
    -- but we only need one direction, thus it is impossible.
  ν-∪`    : ∀ qs zs → ( ν (zs ∪ sucₛₛ qs 0) ) R ( ν zs ∪ qs )
  ν-·`    : ∀ qs zs → ( ν (zs · sucₛₛ qs 0) ) R ( ν zs · qs )
  assoc   : (x y z : SState) → ( x ∪ (y ∪ z) ) R ( (x ∪ y) ∪ z )
  rid     : (x : SState) → ( x ∪ 0b ) R ( x )
  comm    : (x y : SState ) → ( x ∪ y ) R ( y ∪ x )
-- Equal terms here mean that we have equal state, but maybe we can have different actors (locationwise),
-- This also means that actors that the secret of ν does not play a role in the equality here.
-- In other words, as long as the structure is the same, it is the same state.
  idem    : (x : SState) → ( x ∪ x ) R ( x )
  assoc·  : (x y z : SState) → ( x · (y · z) ) R ( (x · y) · z )
  rid·    : (x : SState) → ( x · 1b ) R ( x )
  comm·   : (x y : SState) → ( x · y ) R ( y · x )
  def∅·   : (x : SState) → ( x · 0b ) R ( 0b )
  dist    : (x y z : SState) → ( x · (y ∪ z) ) R ( (x · y) ∪ (x · z) )
  refl`    : ∀ x → x R x
  sym`    : ∀ x y → x R y → y R x
  trans`  : ∀ x y z → x R y → y R z → x R z
  squash₁ : ∀ x y → isProp (x R y)
  



State : Type ℓ
State = SState / _R_

open BinaryRelation

RisPropValued : isPropValued _R_
RisPropValued a b = squash₁ a b

RisEquivRel : isEquivRel _R_
isEquivRel.reflexive RisEquivRel = refl`
isEquivRel.symmetric RisEquivRel = sym`
isEquivRel.transitive RisEquivRel = trans`


All< : ∀{e} → Vec ℕ e → ℕ → Type
All< [] k = Unit
All< (x ∷ xs) k = (x < k) × All< xs k


All<isProp : ∀{e} → (vs : Vec ℕ e) → ∀ n → isProp (All< vs n)
All<isProp [] n = isPropUnit
All<isProp (x ∷ vs) n (a1 , all1) (a2 , all2) = Σ≡Prop (λ _ → All<isProp vs n) (isProp≤ {suc x} {n} a1 a2)

data WellScopedₛₛ : SState → ℕ → Type ℓ where
  ws-0b : ∀{k} → WellScopedₛₛ 0b k
  ws-1b : ∀{k} → WellScopedₛₛ 1b k
  ws-`  : ∀{k n secr c} → All< secr k → WellScopedₛₛ (` ([_]_ {n} secr c)) k
  ws-∪  : ∀{k lq rq} → WellScopedₛₛ lq k → WellScopedₛₛ rq k → WellScopedₛₛ (lq ∪ rq) k
  ws-·  : ∀{k lq rq} → WellScopedₛₛ lq k → WellScopedₛₛ rq k → WellScopedₛₛ (lq · rq) k
  ws-ν  : ∀{k q} → WellScopedₛₛ q (suc k) → WellScopedₛₛ (ν q) k


WSisProp : ∀ s n → isProp (WellScopedₛₛ s n)
WSisProp 0b n ws-0b ws-0b = refl
WSisProp 1b n ws-1b ws-1b = refl
WSisProp (` ([ secr ] _)) n (ws-` x) (ws-` y) = cong ws-` (All<isProp secr n x y)
WSisProp (s ∪ s₁) n (ws-∪ x x₁) (ws-∪ y y₁) = cong₂ ws-∪ (WSisProp s n x y) (WSisProp s₁ n x₁ y₁)
WSisProp (s · s₁) n (ws-· x x₁) (ws-· y y₁) = cong₂ ws-· (WSisProp s n x y) (WSisProp s₁ n x₁ y₁)
WSisProp (ν s) n (ws-ν x) (ws-ν y) = cong ws-ν (WSisProp s (suc n) x y)



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
