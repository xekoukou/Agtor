
{-# OPTIONS --sized-types --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid
open import Cubical.HITs.SetQuotients as Sq
open import Cubical.HITs.PropositionalTruncation as Tr

import MBree
open import SemiRing

module MDerivation {ℓ ℓ'} (C : Type ℓ) (D : Type ℓ') where

open MBree {_} {_} {C} {D}

module Derivation (cm : C → D → Bree) where

  open SemiRingStr (snd BSemiRing)

  δ' : Bree → Bree
  δᵃ' : Bree → Bree → Bree
  δᶜ' : Bree → Bree → Bree

  δᵃ' x y = (δ' x ·  y) ∪ (x · δ' y)

  δᶜ' 0b y = 0b
  δᶜ' 1b y = 0b
  δᶜ' (ƛ f) y = ƛ l1 where
    l1 : _ → Bree
    l1 z = δᶜ' (f z) y
    
  δᶜ' (x1 ∪ x2) y = δᶜ' x1 y ∪ δᶜ' x2 y
  δᶜ' (x1 · x2) y = (δᶜ' x1 y · x2) ∪ (δᶜ' x2 y · x1)
  δᶜ' (x ← y) 0b = 0b
  δᶜ' (x ← y) 1b = 0b
  δᶜ' x@(_ ← _) (y1 ∪ y2) = δᶜ' x y1 ∪ δᶜ' x y2
  δᶜ' x@(_ ← _) (y1 · y2) = (δᶜ' x y1 · y2) ∪ (δᶜ' x y2 · y1)
  δᶜ' (x1 ← y1) (x2 ← y2) = ((cm x1 y2) · (x2 ← y1)) ∪ ((x1 ← y2) · (cm x2 y1))
  δᶜ' x@(_ ← _) (ƛ f) = ƛ λ z → δᶜ' x (f z) 

  δ' 0b = 0b
  δ' 1b = 0b
  δ' (x ← y) = cm x y
  δ' (ƛ x) = ƛ λ z → δ' (x z)
  δ' (x ∪ y) = δ' x ∪ δ' y
  δ' (x · y) = δᵃ' x y ∪ δᶜ' x y

  δ : Bree / ∥S∥ → Bree / ∥S∥
  δᵃ : Bree / ∥S∥ → Bree / ∥S∥ → Bree / ∥S∥
  δᶜ : Bree / ∥S∥ → Bree / ∥S∥ → Bree / ∥S∥

  l1 : (a b : Bree) → ∥S∥ a b → ∥S∥ (δ' a) (δ' b)
  l1 a b r = Tr.elim (λ x → squash) {!!} r where
    l11 : ∀{a b} → (x : S a b) → S (δ' a) (δ' b)
    l11 (assoc x y z) = assoc _ _ _
    l11 (rid _) = rid _
    l11 (comm x y) = comm _ _
    l11 (∪c c x) = ∪c _ (l11 x)
    l11 (idem _) = idem _
    l11 perm = {!!}
    l11 (assoc· x y z) = {!!}
    l11 (rid· _) = {!!}
    l11 (·c c x) = {!!}
    l11 (comm· x y) = {!!}
    l11 (def∅· x) = {!!}
    l11 (defƛ· x y) = {!!}
    l11 (dist` x y z) = {!!}
    l11 (distƛ∪ x y) = {!!}
    l11 (distƛ· x y) = {!!}
    l11 (remƛ _ y x) = {!!}
    l11 (ƛS x) = {!!}
    l11 rel-refl = {!!}
    l11 (rel-sym x) = {!!}
    l11 (rel-trans x y) = {!!}

  l2 : (a b c : Bree) → ∥S∥ a b → ∥S∥ (δᵃ' a c) (δᵃ' b c)
  l2 a b c r = {!!}

  l3 : (a b c : Bree) → ∥S∥ b c → ∥S∥ (δᵃ' a b) (δᵃ' a c)
  l3 a b c r = {!!}

  l4 : (a b c : Bree) → ∥S∥ a b → ∥S∥ (δᶜ' a c) (δᶜ' b c)
  l4 a b c r = {!!}

  l5 : (a b c : Bree) → ∥S∥ b c → ∥S∥ (δᶜ' a b) (δᶜ' a c)
  l5 a b c r = {!!}


  δ x = Sq.rec squash/ (λ z → [ δ' z ]) (λ a b r → eq/ _ _ (l1 a b r)) x
  
  δᵃ x y = Sq.rec2 squash/ (λ x y → [ δᵃ' x y ]) (λ a b c r → eq/ _ _ (l2 a b c r)) (λ a b c r → eq/ _ _ (l3 a b c r)) x y
  
  δᶜ x y = Sq.rec2 squash/ (λ x y → [ δᶜ' x y ]) (λ a b c r → eq/ _ _ (l4 a b c r)) (λ a b c r → eq/ _ _ (l5 a b c r)) x y


--   -- -- δ : Bree / S → Bree / S
--   -- -- δ a = rec squash/ (λ z → [ δ' z ]) (λ a b r → eq/ _ _ (l1 a b r)) a where
--   -- --   l1 : (a b : Bree) → S a b → S (δ' a) (δ' b)
--   -- --   l1 .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = assoc _ _ _
--   -- --   l1 .(b ∪ ∅) b (rid .b) = rid _
--   -- --   l1 .(x ∪ y) .(y ∪ x) (comm x y) = comm _ _
--   -- --   l1 .(_ ∪ c) .(_ ∪ c) (∪c c r) = ∪c _ (l1 _ _ r)
--   -- --   l1 .(b ∪ b) b (idem .b) = idem _
--   -- --   l1 .(x · y · z) .((x · y) · z) (assoc· x y z) = rel-trans l11 l12 where
--   -- --     l11 : S (δ' x · y · z ∪ x · (δ' y · z ∪ y · δ' z)) (x · y · δ' z ∪ x · δ' y · z ∪ δ' x · y · z)
--   -- --     l11 = rel-trans (comm _ _) (rel-trans (∪c _ (rel-trans (dist` _ _ _) (comm _ _))) (rel-sym (assoc _ _ _)))
--   -- --     l12 : S (x · y · δ' z ∪ x · δ' y · z ∪ δ' x · y · z)
--   -- --             ((δ' x · y ∪ x · δ' y) · z ∪ (x · y) · δ' z)
--   -- --     l12 = rel-trans (∪c _ (assoc· _ _ _)) (rel-trans (comm _ _) (∪c _ (rel-trans (comm _ _)
--   -- --           (rel-trans (rel-sym (rel-trans (dist` _ _ _) (rel-trans (∪c _ (rel-trans (comm· _ _) (rel-sym (assoc· _ _ _)))) (rel-trans (comm _ _) (rel-trans (∪c _ (rel-trans (comm· _ _) (rel-sym (assoc· _ _ _)))) (comm _ _)))))) (comm· _ _)))))
--   -- --   l1 .(b · ` CM.ε ) b (rid· .b) = {!!}
--   -- --   l1 .(_ · c) .(_ · c) (·c c r) = {!!}
--   -- --   l1 .(x · y) .(y · x) (comm· x y) = {!!}
--   -- --   l1 .(x · ∅) .∅ (def∅· x) = {!!}
--   -- --   l1 .(` x · ` y) .(` (x CM.· y)) (def· x y) = {!!}
--   -- --   l1 .(x · (ƛ y)) .(ƛ (λ q → x · y q)) (defƛ· x y) = {!!}
--   -- --   l1 .(x · (y ∪ z)) .(x · y ∪ x · z) (dist` x y z) = {!!}
--   -- --   l1 .(ƛ (λ c → x c ∪ y c)) .((ƛ x) ∪ (ƛ y)) (distƛ∪ x y) = {!!}
--   -- --   l1 .(ƛ (λ c → x c · y c)) .((ƛ x) · (ƛ y)) (distƛ· x y) = {!!}
--   -- --   l1 .(ƛ y) b (remƛ .b y x) = {!!}
--   -- --   l1 .(ƛ _) .(ƛ _) (ƛS x) = {!!}
--   -- --   l1 x y (rel-sym r) = rel-sym (l1 _ _ r)
--   -- --   l1 x z (rel-trans r1 r2) = rel-trans (l1 _ _ r1) (l1 _ _ r2)
