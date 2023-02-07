{-# OPTIONS  --confluence-check --sized-types --cubical #-}

module InnerProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Function
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients

open import ProductCommMonoid
import MBree

module _ {ℓ ℓ'} (c1 : CommMonoid ℓ) (c2 : CommMonoid ℓ') where

  c1×c2 = ProductCommMonoid c1 c2

  C = ⟨ c1×c2 ⟩
  
  open MBree {_} {c1×c2}

  module C1 = CommMonoidStr (snd c1)
  module C2 = CommMonoidStr (snd c2)
  module PC = CommMonoidStr (snd c1×c2)

  module CB = CommMonoidStr (snd BCommMonoid)

  pr'₁ : C → C
  pr'₁ (x , y) = C1.ε , y

  pr'₂ : C → C
  pr'₂ (x , y) = x  , C2.ε

  pr₁ : Bree / S → Bree / S
  pr₁ x = rec CB.is-set (λ x → [ l1 x ]) (λ a b r → eq/ _ _ (l2 a b r)) x where
    l1 : Bree → Bree
    l1 ∅ = ∅
    l1 (` x) = ` pr'₁ x
    l1 (ƛ f) = ƛ (λ x → l1 (f x))
    l1 (x ∪ y) = l1 x ∪ l1 y
    l1 (x · y) = l1 x · l1 y

    l2 : (a b : Bree) → S a b → S (l1 a) (l1 b)
    l2 .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = assoc _ _ _
    l2 .(b ∪ ∅) b (rid .b) = rid _
    l2 .(x ∪ y) .(y ∪ x) (comm x y) = comm _ _
    l2 .(_ ∪ c) .(_ ∪ c) (∪c c r) = ∪c _ (l2 _ _ r)
    l2 .(b ∪ b) b (idem .b) = idem _
    l2 .(x · y · z) .((x · y) · z) (assoc· x y z) = assoc· _ _ _
    l2 .(b · ` PC.ε) b (rid· .b) = rid· _
    l2 .(_ · c) .(_ · c) (·c c r) = ·c _ (l2 _ _ r)
    l2 .(x · y) .(y · x) (comm· x y) = comm· _ _
    l2 .(x · ∅) .∅ (def∅· x) = def∅· _
    l2 .(` x · ` y) .(` (x PC.· y)) (def· x y) = subst (λ x → S _ (` (x , _))) (C1.rid _) (def· _ _)
    l2 .(x · (ƛ y)) .(ƛ (λ q → x · y q)) (defƛ· x y) = defƛ· _ _
    l2 .(x · (y ∪ z)) .(x · y ∪ x · z) (dist` x y z) = dist` _ _ _
    l2 .(ƛ (λ c → x c ∪ y c)) .((ƛ x) ∪ (ƛ y)) (distƛ∪ x y) = distƛ∪ _ _
    l2 .(ƛ (λ c → x c · y c)) .((ƛ x) · (ƛ y)) (distƛ· x y) = distƛ· _ _
    l2 .(ƛ y) b (remƛ .b y x) = remƛ _ _ (funExt (λ z i → l1 (x i z)))
    l2 .(ƛ _) .(ƛ _) (ƛS x) = ƛS λ c → l2 _ _ (x c)

  pr₂ : Bree / S → Bree / S
  pr₂ x = rec CB.is-set (λ x → [ l1 x ]) (λ a b r → eq/ _ _ (l2 a b r)) x where
    l1 : Bree → Bree
    l1 ∅ = ∅
    l1 (` x) = ` pr'₂ x
    l1 (ƛ f) = ƛ (λ x → l1 (f x))
    l1 (x ∪ y) = l1 x ∪ l1 y
    l1 (x · y) = l1 x · l1 y

    l2 : (a b : Bree) → S a b → S (l1 a) (l1 b)
    l2 .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = assoc _ _ _
    l2 .(b ∪ ∅) b (rid .b) = rid _
    l2 .(x ∪ y) .(y ∪ x) (comm x y) = comm _ _
    l2 .(_ ∪ c) .(_ ∪ c) (∪c c r) = ∪c _ (l2 _ _ r)
    l2 .(b ∪ b) b (idem .b) = idem _
    l2 .(x · y · z) .((x · y) · z) (assoc· x y z) = assoc· _ _ _
    l2 .(b · ` PC.ε) b (rid· .b) = rid· _
    l2 .(_ · c) .(_ · c) (·c c r) = ·c _ (l2 _ _ r)
    l2 .(x · y) .(y · x) (comm· x y) = comm· _ _
    l2 .(x · ∅) .∅ (def∅· x) = def∅· _
    l2 .(` x · ` y) .(` (x PC.· y)) (def· x y) = subst (λ x → S _ (` (_ , x))) (C2.rid _) (def· _ _)
    l2 .(x · (ƛ y)) .(ƛ (λ q → x · y q)) (defƛ· x y) = defƛ· _ _
    l2 .(x · (y ∪ z)) .(x · y ∪ x · z) (dist` x y z) = dist` _ _ _
    l2 .(ƛ (λ c → x c ∪ y c)) .((ƛ x) ∪ (ƛ y)) (distƛ∪ x y) = distƛ∪ _ _
    l2 .(ƛ (λ c → x c · y c)) .((ƛ x) · (ƛ y)) (distƛ· x y) = distƛ· _ _
    l2 .(ƛ y) b (remƛ .b y x) = remƛ _ _ (funExt (λ z i → l1 (x i z)))
    l2 .(ƛ _) .(ƛ _) (ƛS x) = ƛS λ c → l2 _ _ (x c)

  {-# TERMINATING #-}
  multi : Bree → Bree → Bree
  multi x ∅ = ∅
  multi x (` y) = x · (` y)
  multi x (ƛ f) = ƛ λ z → x · f z
  multi x (y1 ∪ y2) = (x · y1) ∪ (x · y2)
  multi x (y1 · y2) = multi x (multi y1 y2)

  ww : Bree → Bree → Bree
  ww ∅ y = ∅
  ww (` x) ∅ = ∅
  ww (` x) (` y) = (` x) · (` y)
  ww (` x) (ƛ f) = ƛ λ z → ww (` x) (f z)
  ww (` x) (y ∪ _) = ww (` x) y
  ww (` x) (y1 · y2) = ww (ww (` x) y1) y2
  ww (ƛ f) y = ƛ λ z → ww (f z) y
  ww (x1 ∪ x2) ∅ = ∅
  ww (x1 ∪ x2) (` y) = {!!}
  ww (x1 ∪ x2) (ƛ y) = {!!}
  ww (x1 ∪ x2) (y1 ∪ y2) = {!!}
  ww (x1 ∪ x2) (y1 · y2) = {!!}
  ww (x1 · x2) y = {!!}
