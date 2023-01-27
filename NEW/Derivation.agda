{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Vec as V
open import Cubical.Data.List as L
open import Cubical.Data.Maybe
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin
import Cubical.Data.FinData as FD
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

module Derivation {ℓ ℓ' : _} (prM : UMTypePr ℓ ℓ') where

open ActorM prM

-- We can reduce messages under a specific scope if the actors can only receive message with the specified secrets
-- and there is no message that sends the secret to a new actor.
-- or if the actor does not accept the specific message with the secret due to the predicate being false.

module _ where

  open StV

  δₛₛ[_] : ∀{fv k} → Secret k → SState fv → Maybe (SState fv)
  δₛₛ[ s ] 0b = just 0b
  δₛₛ[ s ] 1b = just 1b
  δₛₛ[ s ] (` x) = {!!}
  δₛₛ[ s ] (q ∪ q₁) = {!δₛₛ[ s ] q ∪ δₛₛ[ s ] q₁!}
  δₛₛ[ s ] (q · q₁) = {!!}
  δₛₛ[ s ] (ν q) = {!!}



  l1 : ∀ {fv} {k1} {k2} (secr1 : Vec ℕ k1) (s : Secret k1)
         (secr2 : Vec ℕ k2) {AT : ActorT k2} (a : Actor AT) →
       SState fv
  l1 secr1 record { cond = cond ; nsecr = nsecr ; secr = secr } secr2 a = {!!} where
    nSs = V.map (λ (a , b) → lookup (FD.fromℕ' _ a b) secr1) secr
    l3 = V.map (λ x → (x , true)) secr1
    l4 = V.foldr (λ (a , b) y → replace (λ (x , y) → x , false) (FD.fromℕ' _ a b) y) l3 secr
    cs = V.foldr (λ { (x , false) y → y ; (x , true) y → x ∷ y}) L.[] l4

    

  mutual

    δₛₛ : ∀{fv} → SState fv → SState fv
    δₛₛ 0b = 0b
    δₛₛ 1b = 1b
    δₛₛ (` [ secr ] c-s x) = 0b
    δₛₛ (` [ secr ] c-m MT x) = 0b
    δₛₛ (` [ secr ] c-a AT a) = ? -- Actor.δ a
    δₛₛ (q ∪ q₁) = δₛₛ q ∪ δₛₛ q₁
    δₛₛ (lq · rq) = δᵃₛₛ lq rq ∪ δᶜₛₛ lq rq
    δₛₛ (ν q) = ν δₛₛ q
  
  
    δᵃₛₛ : ∀{fv} → SState fv → SState fv → SState fv
    δᵃₛₛ x y = δₛₛ x · y ∪ (x · δₛₛ y)


    δᶜₛₛ : ∀{fv} → SState fv → SState fv → SState fv
    δᶜₛₛ 0b rq = 0b
    δᶜₛₛ 1b rq = 0b
    δᶜₛₛ lq@(` x) 0b = 0b
    δᶜₛₛ lq@(` x) 1b = 0b
    δᶜₛₛ (` [ secr1 ] c1) (` [ secr2 ] c2) = δᶜ`ₛₛ secr1 c1 secr2 c2
    δᶜₛₛ lq@(` x) (rq1 ∪ rq2) = δᶜₛₛ lq rq1 ∪ δᶜₛₛ lq rq2
    δᶜₛₛ lq@(` x) (rq1 · rq2) = δᶜₛₛ lq rq1 · rq2 ∪ rq1 · δᶜₛₛ lq rq2
    δᶜₛₛ lq@(` x) (ν rq) = δᶜₛₛ lq rq
    δᶜₛₛ (lq1 ∪ lq2) rq = δᶜₛₛ lq1 rq ∪ δᶜₛₛ lq2 rq
    δᶜₛₛ (lq1 · lq2) rq = δᶜₛₛ lq1 rq · lq2 ∪ lq1 · δᶜₛₛ lq2 rq
    δᶜₛₛ (ν lq) rq = ν δᶜₛₛ lq (sucₛₛ rq 0)


    δᶜ`ₛₛ : ∀{fv k1 k2} → (secr1 : Vec ℕ k1) (c1 : C k1)
            (secr2 : Vec ℕ k2) (c2 : C k2) → SState fv
    δᶜ`ₛₛ secr1 (c-s x) secr2 (c-s x₁) = 0b
    δᶜ`ₛₛ secr1 (c-s x) secr2 (c-m MT x₁) = 0b
    δᶜ`ₛₛ secr1 (c-s s) secr2 (c-a AT a) = {!l1 secr1 s secr2 a!}
    δᶜ`ₛₛ secr1 (c-m MT m) secr2 (c-s x₁) = 0b
    δᶜ`ₛₛ secr1 (c-m MT x) secr2 (c-m MT₁ x₁) = 0b
    δᶜ`ₛₛ secr1 (c-m MT m) secr2 (c-a AT a) = {!!}
    δᶜ`ₛₛ secr1 (c-a AT x) secr2 (c-s x₁) = {!!}
    δᶜ`ₛₛ secr1 (c-a AT x) secr2 (c-m MT x₁) = {!!}
    δᶜ`ₛₛ secr1 (c-a AT x) secr2 (c-a AT₁ x₁) = 0b


