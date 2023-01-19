{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Maybe
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients as SQ renaming ([_] to ⟨_⟩ₛ)
import State
import ActorM
open import Projection

module Delta {ℓ ℓ' : _} (prM : UMTypePr ℓ ℓ') where

open ActorM prM

-- We can reduce messages under a specific scope if the actors can only receive message with the specified secrets
-- and there is no message that sends the secret to a new actor.
-- or if the actor does not accept the specific message with the secret due to the predicate being false.

module _ where

  open StV

  δₛₛ[_] : ∀{k} → Secret k → SState → Maybe SState
  δₛₛ[ s ] 0b = just 0b
  δₛₛ[ s ] 1b = just 1b
  δₛₛ[ s ] (` x) = {!!}
  δₛₛ[ s ] (q ∪ q₁) = {!δₛₛ[ s ] q ∪ δₛₛ[ s ] q₁!}
  δₛₛ[ s ] (q · q₁) = {!!}
  δₛₛ[ s ] (ν q) = {!!}

  mutual

    δₛₛ : ℕ → SState → SState
    δₛₛ l 0b = 0b
    δₛₛ l 1b = 1b
    δₛₛ l (` [ secr ] c-s x) = 0b
    δₛₛ l (` [ secr ] c-m MT x) = 0b
    δₛₛ l (` [ secr ] c-a AT a) = fst (Actor.δ a)
    δₛₛ l (q ∪ q₁) = δₛₛ l q ∪ δₛₛ l q₁
    δₛₛ l (lq · rq) = δᵃₛₛ l l lq rq ∪ δᶜₛₛ l l lq rq
    δₛₛ l (ν q) = δₛₛ (suc l) q
  
  
    δᵃₛₛ : ∀ l r → SState → SState → SState
    δᵃₛₛ l r x y = δₛₛ l x · y ∪ (x · δₛₛ r y)


    δᶜₛₛ : ∀ l r → SState → SState → SState
    δᶜₛₛ l r 0b rq = 0b
    δᶜₛₛ l r 1b rq = 0b
    δᶜₛₛ l r lq@(` x) 0b = 0b
    δᶜₛₛ l r lq@(` x) 1b = 0b
    δᶜₛₛ l r (` [ secr1 ] c1) (` [ secr2 ] c2) = δᶜ`ₛₛ l r secr1 c1 secr2 c2
    δᶜₛₛ l r lq@(` x) (rq1 ∪ rq2) = δᶜₛₛ l r lq rq1 ∪ δᶜₛₛ l r lq rq2
    δᶜₛₛ l r lq@(` x) (rq1 · rq2) = δᶜₛₛ l r lq rq1 · rq2 ∪ rq1 · δᶜₛₛ l r lq rq2
    δᶜₛₛ l r lq@(` x) (ν rq) = δᶜₛₛ l (suc r) lq rq
    δᶜₛₛ l r (lq1 ∪ lq2) rq = δᶜₛₛ l r lq1 rq ∪ δᶜₛₛ l r lq2 rq
    δᶜₛₛ l r (lq1 · lq2) rq = δᶜₛₛ l r lq1 rq · lq2 ∪ lq1 · δᶜₛₛ l r lq2 rq
    δᶜₛₛ l r (ν lq) rq = δᶜₛₛ (suc l) r lq rq


    δᶜ`ₛₛ : ∀{k1 k2} → ∀ (l r : ℕ) (secr1 : Vec ℕ k1) (c1 : C k1)
           (secr2 : Vec ℕ k2) (c2 : C k2) → SState
    δᶜ`ₛₛ l r secr1 (ActorM.c-s x) secr2 (ActorM.c-s x₁) = 0b
    δᶜ`ₛₛ l r secr1 (ActorM.c-s x) secr2 (ActorM.c-m MT x₁) = 0b
    δᶜ`ₛₛ l r secr1 (ActorM.c-s s) secr2 (ActorM.c-a AT a) = {!!}
    δᶜ`ₛₛ l r secr1 (ActorM.c-m MT m) secr2 (ActorM.c-s x₁) = 0b
    δᶜ`ₛₛ l r secr1 (ActorM.c-m MT x) secr2 (ActorM.c-m MT₁ x₁) = 0b
    δᶜ`ₛₛ l r secr1 (ActorM.c-m MT m) secr2 (ActorM.c-a AT a) = {!!}
    δᶜ`ₛₛ l r secr1 (ActorM.c-a AT x) secr2 (ActorM.c-s x₁) = {!!}
    δᶜ`ₛₛ l r secr1 (ActorM.c-a AT x) secr2 (ActorM.c-m MT x₁) = {!!}
    δᶜ`ₛₛ l r secr1 (ActorM.c-a AT x) secr2 (ActorM.c-a AT₁ x₁) = 0b
