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
 -- first argument is the secrets of the msg
 -- returns the position of the secret to the actor list of secrets.
compSecr : ∀{fv k1 k2} → Vec (Fin fv) k1 → Vec (Fin fv) k2 → Maybe (List (Fin k2))
compSecr [] ys = just []
compSecr (x ∷ xs) ys = (compS x ys) >>=M λ x → compSecr xs ys >>=M λ ys → just (x ∷ ys) where
  compS : ∀ {fv} {k2} (x : Fin fv) (ys : Vec (Fin fv) k2) → Maybe (Fin k2)
  compS x [] = nothing
  compS x (y ∷ ys) with fst x =? fst y
  ... | yes p = just fzero
  ... | no ¬p = compS x ys >>=M λ x → just (fsuc x)



module _ where

  open StV

  open MsgT
  open ActorT
  open Actor

  acceptMsg? : ∀ {fv} {kₘ} {kₐ} (secrₘ : Vec (Fin fv) kₘ) (MT : MsgT kₘ) →
         (secrₐ : Vec (Fin fv) kₐ) (AT : ActorT kₐ) → Maybe (Vec (Fin fv) (toℕ (nsecr MT)) × (Σ (List (Fin kₐ)) λ c → P AT c (toℕ (nsecr MT)) (umT MT)))
  acceptMsg? {fv} secrₘ MT secrₐ AT with compSecr (snd (let (n , rl) = nsecr MT in V.split (FD.fromℕ' _ n rl) secrₘ)) secrₐ
  ... | nothing = nothing
  ... | just ls with decP AT ls (toℕ (nsecr MT)) (umT MT)
  ... | yes p = just (nSecr , ls , p ) where
    q = let (n , rl) = nsecr MT in fst (V.split (FD.fromℕ' _ n rl) secrₘ)
    nSecr = subst (λ x → Vec (Fin fv) x) (FD.toFromId' (suc _) (fst (nsecr MT)) (snd (nsecr MT))) q
  ... | no ¬p = nothing

    

  actor-δᶜV : ∀ {fv} {kₘ} {kₐ} → (secrₘ : Vec (Fin fv) kₘ) → (MT : MsgT kₘ) → ⟨ ⟦ MsgT.umT MT ⟧ ⟩ →
         (secrₐ : Vec (Fin fv) kₐ) → (AT : ActorT kₐ) → (a : Actor AT) → SState fv
  actor-δᶜV {fv} {kₘ} {kₐ} secrₘ MT x secrₐ AT a with acceptMsg? secrₘ MT secrₐ AT
  ... | nothing = 0b
  ... | just (nSecr , c , p) = substₛₛ (secrₐ V.++ nSecr) q where
    q = fst ((δᶜ a) c (toℕ (nsecr MT)) (umT MT) {p = ∣ p ∣₁} x)
    

  mutual

    δₛₛ : ∀{fv} → SState fv → SState fv
    δₛₛ 0b = 0b
    δₛₛ 1b = 0b
    δₛₛ (` [ secr ] c-m MT x) = 0b
    δₛₛ (` [ secr ] c-a AT a) = substₛₛ secr (fst (Actor.δ a))
    δₛₛ (q ∪ q₁) = δₛₛ q ∪ δₛₛ q₁
    δₛₛ (lq · rq) = δᵃₛₛ lq rq ∪ δᶜₛₛ lq rq
    δₛₛ (ν q) = ν δₛₛ q
  
  
    δᵃₛₛ : ∀{fv} → SState fv → SState fv → SState fv
    δᵃₛₛ x y = δₛₛ x · y ∪ (x · δₛₛ y)

    {-# TERMINATING #-}
    δᶜₛₛ : ∀{fv} → SState fv → SState fv → SState fv
    δᶜₛₛ 0b rq = 0b
    δᶜₛₛ 1b rq = 0b
    δᶜₛₛ lq@(` x) 0b = 0b
    δᶜₛₛ lq@(` x) 1b = 0b
    δᶜₛₛ (` [ secr1 ] c1) (` [ secr2 ] c2) = δᶜ`ₛₛ secr1 c1 secr2 c2
    δᶜₛₛ lq@(` x) (rq1 ∪ rq2) = δᶜₛₛ lq rq1 ∪ δᶜₛₛ lq rq2
    δᶜₛₛ lq@(` x) (rq1 · rq2) = δᶜₛₛ lq rq1 · rq2 ∪ rq1 · δᶜₛₛ lq rq2
    δᶜₛₛ lq@(` x) (ν rq) = ν δᶜₛₛ (sucₛₛ lq 0) rq
    δᶜₛₛ (lq1 ∪ lq2) rq = δᶜₛₛ lq1 rq ∪ δᶜₛₛ lq2 rq
    δᶜₛₛ (lq1 · lq2) rq = δᶜₛₛ lq1 rq · lq2 ∪ lq1 · δᶜₛₛ lq2 rq
    δᶜₛₛ (ν lq) rq = ν δᶜₛₛ lq (sucₛₛ rq 0)


    δᶜ`ₛₛ : ∀{fv k1 k2} → (secr1 : Vec (Fin fv) k1) (c1 : C k1)
            (secr2 : Vec (Fin fv) k2) (c2 : C k2) → SState fv
    δᶜ`ₛₛ secr1 (c-m MT x) secr2 (c-m MT₁ x₁) = 0b
    δᶜ`ₛₛ secr1 (c-m MT m) secr2 (c-a AT a) =  actor-δᶜV secr1 MT m secr2 AT a  
    δᶜ`ₛₛ secr1 (c-a AT a) secr2 (c-m MT m) = actor-δᶜV secr2 MT m secr1 AT a  
    δᶜ`ₛₛ secr1 (c-a AT x) secr2 (c-a AT₁ x₁) = 0b



  mutual
      δₛₛR : ∀ {fv} (a b : SState fv) (r : a R b) → δₛₛ a R δₛₛ b
      δₛₛR .(_ ∪ _) .(_ ∪ _) (⟨⟩-∪ r r₁) = ⟨⟩-∪ (δₛₛR _ _ r) (δₛₛR _ _ r₁)
      δₛₛR (lq1 · rq1) (lq2 · rq2) (⟨⟩-· r r₁) = ⟨⟩-∪ (trans` (δᵃₛₛ _ _) (δᵃₛₛ _ _) (δᵃₛₛ _ _) (δᵃₛₛRl _ _ _ r) (δᵃₛₛRr _ _ _ r₁)) (trans` (δᶜₛₛ lq1 rq1) (δᶜₛₛ lq2 rq1) (δᶜₛₛ lq2 rq2) (δᶜₛₛRl  lq1 lq2 rq1 r) (δᶜₛₛRr rq1 rq2 lq2 r₁))
      δₛₛR .(ν _) .(ν _) (⟨⟩-ν r) = ⟨⟩-ν (δₛₛR _ _ r)
      δₛₛR .(ν (ν swapₛₛ 0 1 qs)) .(ν (ν qs)) (ν-swap` qs) = {!!}
      δₛₛR .(ν sucₛₛ b 0) b (ν-elim` .b) = {!!}
      δₛₛR .(ν (zs ∪ qs)) .(ν zs ∪ ν qs) (ν-∪` qs zs) = {!!}
      δₛₛR .(ν (zs · sucₛₛ qs 0)) .(ν zs · qs) (ν-·` qs zs) = {!!}
      δₛₛR .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = {!!}
      δₛₛR .(b ∪ 0b) b (rid .b) = {!!}
      δₛₛR .(x ∪ y) .(y ∪ x) (comm x y) = {!!}
      δₛₛR .(b ∪ b) b (idem .b) = {!!}
      δₛₛR .(x · y · z) .((x · y) · z) (assoc· x y z) = {!!}
      δₛₛR .(b · 1b) b (rid· .b) = {!!}
      δₛₛR .(x · y) .(y · x) (comm· x y) = {!!}
      δₛₛR .(x · 0b) .0b (def∅· x) = {!!}
      δₛₛR .(x · (y ∪ z)) .(x · y ∪ x · z) (dist x y z) = {!!}
      δₛₛR a .a (refl` .a) = {!!}
      δₛₛR a b (sym` .b .a r) = {!!}
      δₛₛR a b (trans` .a y .b r r₁) = {!!}
      δₛₛR a b (squash₁ .a .b r r₁ i) = {!!}

      δᵃₛₛRl : ∀ {fv} (a b c : SState fv) (r : a R b) → δᵃₛₛ a c R δᵃₛₛ b c
      δᵃₛₛRl = {!!}
      δᵃₛₛRr : ∀ {fv} (a b c : SState fv) (r : a R b) → δᵃₛₛ c a R δᵃₛₛ c b
      δᵃₛₛRr = {!!}
      δᶜₛₛRl : ∀ {fv} (a b c : SState fv) (r : a R b) → δᶜₛₛ a c R δᶜₛₛ b c
      δᶜₛₛRl = {!!}
      δᶜₛₛRr : ∀ {fv} (a b c : SState fv) (r : a R b) → δᶜₛₛ c a R δᶜₛₛ c b
      δᶜₛₛRr = {!!}



  δₛ : ∀{fv} → State fv → State fv
  δₛ q = SQ.rec SQ.squash/ (λ x → ⟨ δₛₛ x ⟩ₛ) (λ a b r → eq/ (δₛₛ a) (δₛₛ b) (δₛₛR a b r)) q


  δᵃₛ : ∀{fv} → State fv → State fv → State fv
  δᵃₛ lq rq = SQ.rec2 SQ.squash/ (λ x y → ⟨ δᵃₛₛ x y ⟩ₛ) (λ a b c r → eq/ (δᵃₛₛ a c) (δᵃₛₛ b c) (δᵃₛₛRl a b c r)) (λ a b c r → eq/ (δᵃₛₛ a b) (δᵃₛₛ a c) (δᵃₛₛRr b c a r)) lq rq

  δᶜₛ : ∀{fv} → State fv → State fv → State fv
  δᶜₛ lq rq = SQ.rec2 SQ.squash/ (λ x y → ⟨ δᶜₛₛ x y ⟩ₛ) (λ a b c r → eq/ (δᶜₛₛ a c) (δᶜₛₛ b c) (δᶜₛₛRl a b c r)) (λ a b c r → eq/ (δᶜₛₛ a b) (δᶜₛₛ a c) (δᶜₛₛRr b c a r)) lq rq
