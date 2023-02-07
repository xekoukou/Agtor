{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Structure
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

-- We expect the world to be non-terminating under all cases. This needs to be proved in parallel with δ.

-- We can reduce messages under a specific scope if the actors can only receive message with the specified secrets
-- and there is no message that sends the secret to a new actor.
-- or if the actor does not accept the specific message with the secret due to the predicate being false.


 -- All old Secrets should be known to the actor.
compare : ∀{fv k1 k2} → Vec (Fin fv) k1 → Vec (Fin fv) k2 → Maybe (List (Fin k2))
compare [] ys = just []
compare (x ∷ xs) ys = (comp2 x ys) >>=M λ x → compare xs ys >>=M λ ys → just (x ∷ ys) where
  comp2 : ∀ {fv} {k2} (x : Fin fv) (ys : Vec (Fin fv) k2) → Maybe (Fin k2)
  comp2 x [] = nothing
  comp2 x (y ∷ ys) with fst x =? fst y
  ... | yes p = just fzero
  ... | no ¬p = comp2 x ys >>=M λ x → just (fsuc x)



module _ where

  open StV

  δₛₛ[_] : ∀{fv} → Fin fv → SState fv → Maybe (SState fv)
  δₛₛ[ s ] 0b = just 0b
  δₛₛ[ s ] 1b = just 1b
  δₛₛ[ s ] (` x) = {!!}
  δₛₛ[ s ] (q ∪ q₁) = {!δₛₛ[ s ] q ∪ δₛₛ[ s ] q₁!}
  δₛₛ[ s ] (q · q₁) = {!!}
  δₛₛ[ s ] (ν q) = {!!}


  open MsgT
  open ActorT
  open Actor

  l2 : ∀ {fv} {kₘ} {kₐ} (secrₘ : Vec (Fin fv) kₘ) (MT : MsgT kₘ) →
         (secrₐ : Vec (Fin fv) kₐ) (AT : ActorT kₐ) → Maybe (Vec (Fin fv) (toℕ (nsecr MT)) × (Σ (List (Fin kₐ)) λ c → P AT c (toℕ (nsecr MT)) (umT MT)))
  l2 {fv} secrₘ MT secrₐ AT with compare (snd (let (n , rl) = nsecr MT in V.split (FD.fromℕ' _ n rl) secrₘ)) secrₐ
  ... | nothing = nothing
  ... | just ls with decP AT ls (toℕ (nsecr MT)) (umT MT)
  ... | yes p = just (nSecr , ls , p ) where
    q = let (n , rl) = nsecr MT in V.split (FD.fromℕ' _ n rl) secrₘ
    nSecr = subst (λ x → Vec (Fin fv) x) (FD.toFromId' (suc _) (fst (nsecr MT)) (snd (nsecr MT))) (fst q)
  ... | no ¬p = nothing

    

  l1 : ∀ {fv} {kₘ} {kₐ} → (secrₘ : Vec (Fin fv) kₘ) → (MT : MsgT kₘ) → ⟨ ⟦ MsgT.umT MT ⟧ ⟩ →
         (secrₐ : Vec (Fin fv) kₐ) → (AT : ActorT kₐ) → (a : Actor AT) → SState (toℕ (nsecr MT) + kₐ)
  l1 {fv} {kₘ} {kₐ} secrₘ MT x secrₐ AT a with l2 secrₘ MT secrₐ AT
  ... | nothing = 0b
  ... | just (nSecr , c , p) = {!!} where
    q = fst ((δᶜ a) c (toℕ (nsecr MT)) (umT MT) {p = ∣ p ∣₁} x)
    

  mutual

    δₛₛ : ∀{fv} → SState fv → SState fv
    δₛₛ 0b = 0b
    δₛₛ 1b = 1b
    δₛₛ (` [ secr ] c-m MT x) = 0b
    δₛₛ (` [ secr ] c-a AT a) = {!!} -- Actor.δ a
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
    δᶜₛₛ lq@(` x) (ν rq) = {!!} -- ν δᶜₛₛ (sucₛₛ lq 0) rq
    δᶜₛₛ (lq1 ∪ lq2) rq = δᶜₛₛ lq1 rq ∪ δᶜₛₛ lq2 rq
    δᶜₛₛ (lq1 · lq2) rq = δᶜₛₛ lq1 rq · lq2 ∪ lq1 · δᶜₛₛ lq2 rq
    δᶜₛₛ (ν lq) rq = ν δᶜₛₛ lq (sucₛₛ rq 0)


    δᶜ`ₛₛ : ∀{fv k1 k2} → (secr1 : Vec (Fin fv) k1) (c1 : C k1)
            (secr2 : Vec (Fin fv) k2) (c2 : C k2) → SState fv
    δᶜ`ₛₛ secr1 (c-m MT x) secr2 (c-m MT₁ x₁) = 0b
    δᶜ`ₛₛ secr1 (c-m MT m) secr2 (c-a AT a) = {!!}
    δᶜ`ₛₛ secr1 (c-a AT x) secr2 (c-m MT x₁) = {!!}
    δᶜ`ₛₛ secr1 (c-a AT x) secr2 (c-a AT₁ x₁) = 0b


