{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

import MBree
open import SemiRing

module MDerivation {ℓ ℓ'} (C : Type ℓ) (D : Type ℓ') where

open MBree {_} {_} {C} {D}

module Derivation (cm : C → D → Bree) (decm : (x : C) → (y : D) → Dec (cm x y ≡ 0b)) where

  open SemiRingStr (snd BreeSemiRing)

  δᶜ : Bree → Bree → Bree
  δᶜ-0b : (x : Bree) → δᶜ x 0b ≡ 0b
  δᶜ-1b : (x : Bree) → δᶜ x 1b ≡ 0b
  δᶜ-comm : (x y : Bree) → δᶜ x y ≡ δᶜ y x
  δᶜ-linr : ∀ x y z → δᶜ x (y ∪ z) ≡ δᶜ x y ∪ δᶜ x z
  δᶜ-ƛ : ∀ y → {B` : Type} (f : B` → Bree) →{!isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet ?) (δᶜ-permq2 x1 y1 x2 y2 a) (δᶜ-permq2 x1 y1 x2 y2 b) (cong (δᶜ-permq2 x1 y1 x2 y2) p1) (cong (δᶜ-permq2 x1 y1 x2 y2) p2) (squash a b p1 p2) i j!} -- isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet ?) (δᶜ-permq2 x1 y1 x2 y2 a) (δᶜ-permq2 x1 y1 x2 y2 b) (cong (δᶜ-permq2 x1 y1 x2 y2) p1) (cong (δᶜ-permq2 x1 y1 x2 y2) p2) (squash a b p1 p2) i j
         (ƛ (λ z → δᶜ y (f z))) ≡ δᶜ y (ƛ f)
  δᶜ-permq  : ∀ x1 y1 x2 y2 q → δᶜ (x1 ← y1) q · x2 ← y2 ∪ δᶜ (x2 ← y2) q · x1 ← y1 ≡ δᶜ (x1 ← y2) q · x2 ← y1 ∪ δᶜ (x2 ← y1) q · x1 ← y2

  δᶜ-permq2  : ∀ x1 y1 x2 y2 q → δᶜ (x1 ← y1) q · x2 ← y2 ∪ δᶜ (x2 ← y2) q · x1 ← y1 ≡ δᶜ (x1 ← y2) q · x2 ← y1 ∪ δᶜ (x2 ← y1) q · x1 ← y2
  
  δᶜ-linr x y z = δᶜ-comm x (y ∪ z) ∙ cong₂ _∪_ (δᶜ-comm y x) (δᶜ-comm z x)

 --  {-# TERMINATING #-}
  δᶜ 0b y = 0b
  δᶜ 1b y = 0b
  δᶜ (ƛ f) y = ƛ λ z → δᶜ (f z) y
  δᶜ (x1 ∪ x2) y = δᶜ x1 y ∪ δᶜ x2 y
  δᶜ (x1 · x2) y = (δᶜ x1 y · x2) ∪ (δᶜ x2 y · x1)
  δᶜ (z ← q) 0b = 0b
  δᶜ (z ← q) 1b = 0b
  δᶜ (x1 ← y1) (x2 ← y2) = cm x1 y2 · x2 ← y1 ∪ x1 ← y2 · cm x2 y1
  δᶜ x@(z ← q) (ƛ f) = ƛ λ z → δᶜ x (f z)
  δᶜ x@(z ← q) (y1 ∪ y2) = δᶜ x y1 ∪ δᶜ x y2
  δᶜ x@(z ← q) (y1 · y2) = (δᶜ x y1 · y2) ∪ (δᶜ x y2 · y1)
  δᶜ x@(z ← q) (squash a b p1 p2 i j) = isOfHLevel→isOfHLevelDep 2 (λ x → squash)  (δᶜ x a) (δᶜ x b) (cong (δᶜ x) p1) (cong (δᶜ x) p2) (squash a b p1 p2) i j
  δᶜ q@(_ ← _) (assoc {x} {y} {z} i) =  assoc {δᶜ q x} {δᶜ q y} {δᶜ q z} i
  δᶜ q@(_ ← _) (rid {x} i) =  rid {δᶜ q x} i
  δᶜ q@(_ ← _) (comm {x} {y} i) =  comm {δᶜ q x} {δᶜ q y} i
  δᶜ q@(_ ← _) (idem {x} i) = idem {δᶜ q x} i
  δᶜ q@(q1 ← w1) (perm {x1} {y1} {x2} {y2} i) = l1 i module LM where
    l1 = cong₂ _∪_ (ldist {x = x2 ← y2} {y = cm q1 y1 · x1 ← w1} {z = q1 ← y1 · cm x1 w1}) (ldist {x = x1 ← y1} {y = cm q1 y2 · x2 ← w1} {z = q1 ← y2 · cm x2 w1})
        ∙ assoc ∙ cong (_∪ (q1 ← y2 · cm x2 w1) · x1 ← y1) (sym assoc ∙ comm ∙ cong (_∪ (cm q1 y1 · x1 ← w1) · x2 ← y2) (comm ∙ cong₂ _∪_ (sym assoc· ∙ cong (cm q1 y2 ·_) (perm ∙ comm·) ∙ assoc·) (cong (_· x2 ← y2) comm· ∙ sym assoc· ∙ cong (cm x1 w1 ·_) perm ∙ assoc· ∙ cong (_· x2 ← y1) comm·) ∙ sym ldist))
        ∙ sym assoc ∙ cong ((cm q1 y2 · x1 ← w1 ∪ q1 ← y2 · cm x1 w1) · x2 ← y1 ∪_) (cong₂ _∪_ (sym assoc· ∙ cong (cm q1 y1 ·_) (perm ∙ comm·) ∙ assoc·)
          (cong (_· x1 ← y1) comm· ∙ sym assoc· ∙ cong (cm x2 w1 ·_) perm ∙ assoc· ∙ cong (_· x1 ← y2) comm·) ∙ sym ldist)

  δᶜ q@(_ ← _) (assoc· {x} {y} {z} i) =  (cong (λ a → δᶜ q x · y · z ∪ a) (ldist {x} {δᶜ q y · z} {δᶜ q z · y})
    ∙ (cong₂ (λ a b → δᶜ q x · y · z ∪ a ∪ b) ((sym assoc·) ∙ cong (λ a → δᶜ q y · a) comm·) (((sym assoc·) ∙ cong (λ a → δᶜ q z · a) comm·)) ∙ assoc ∙ cong (λ a → a ∪ (δᶜ q z · x · y)) ((cong (λ a → a ∪ (δᶜ q y · x · z)) assoc· ∙ cong (λ a → (δᶜ q x · y) · z ∪ a) assoc·) ∙ sym ldist))) i
  δᶜ q@(_ ← _) (rid· {x} i) = (cong (λ a → δᶜ q x · 1b ∪ a) (ldef∅· {x}) ∙ rid ∙ rid·) i
  δᶜ q@(_ ← _) (comm· {x} {y} i) =  comm {δᶜ q x · y} {δᶜ q y · x} i
  δᶜ q@(_ ← _) (def∅· {x} i) = (cong (λ a →  δᶜ q x · 0b ∪ a) (ldef∅· {x}) ∙ rid ∙ def∅·) i
  δᶜ q@(_ ← _) (dist {x} {y} {z} i) = (cong (λ a → a ∪ ((δᶜ q y ∪ δᶜ q z) · x)) (dist {δᶜ q x} {y} {z})
      ∙ cong (λ a → (δᶜ q x · y ∪ δᶜ q x · z) ∪ a) (ldist {x} {δᶜ q y} {δᶜ q z}) ∙ assoc
      ∙ cong (λ a → (a ∪ δᶜ q y · x) ∪ δᶜ q z · x) comm
      ∙ cong (λ a → a ∪ δᶜ q z · x) (sym (assoc))
      ∙ cong (λ a → a ∪ δᶜ q z · x) comm
      ∙ sym assoc) i
  δᶜ q@(_ ← _) (distƛ∪ {C} {x} {y} i) = distƛ∪ {_} {λ z → δᶜ q (x z)} {λ z → δᶜ q (y z)} i
  δᶜ q@(_ ← _) (distƛ· {C} {x} {y} i) = (distƛ∪ {C} {λ z → δᶜ q (x z) · y} {λ z → δᶜ q y · x z} ∙ cong₂ _∪_ distƛ·  ldistƛ·) i 
  δᶜ q@(_ ← _) (remƛ {C} x i) =  remƛ {C} (δᶜ q x) i
  δᶜ q@(_ ← _) (commƛ f i) = commƛ (λ e v → δᶜ q (f e v)) i
  δᶜ (squash a b p1 p2 i j) y = isOfHLevel→isOfHLevelDep 2 (λ x → squash)  (δᶜ a y) (δᶜ b y) (cong (λ z → δᶜ z y) p1) (cong (λ z → δᶜ z y) p2) (squash a b p1 p2) i j
  δᶜ (assoc {x} {y} {z} i) q = assoc {δᶜ x q} {δᶜ y q} {δᶜ z q} i
  δᶜ (rid {x} i) q = rid {δᶜ x q} i
  δᶜ (comm {x} {y} i) q = comm {δᶜ x q} {δᶜ y q} i
  δᶜ (idem {x} i) q = idem {δᶜ x q} i
  δᶜ (perm {x1} {y1} {x2} {y2} i) q = δᶜ-permq2 x1 y1 x2 y2 q i -- δᶜ-permq x1 y1 x2 y2 q i
  δᶜ (assoc· {x} {y} {z} i) q = (cong (λ a → δᶜ x q · y · z ∪ a) (ldist {x} {δᶜ y q · z} {δᶜ z q · y})
    ∙ (cong₂ (λ a b → δᶜ x q · y · z ∪ a ∪ b) ((sym assoc·) ∙ cong (λ a → δᶜ y q · a) comm·) (((sym assoc·) ∙ cong (λ a → δᶜ z q · a) comm·)) ∙ assoc ∙ cong (λ a → a ∪ (δᶜ z q · x · y)) ((cong (λ a → a ∪ (δᶜ y q · x · z)) assoc· ∙ cong (λ a → (δᶜ x q · y) · z ∪ a) assoc·) ∙ sym ldist))) i
  δᶜ (rid· {x} i) q = (cong (λ a → δᶜ x q · 1b ∪ a) (ldef∅· {x}) ∙ rid ∙ rid·) i
  δᶜ (comm· {x} {y} i) q = comm {δᶜ x q · y} {δᶜ y q · x} i
  δᶜ (def∅· {x} i) q = (cong (λ a →  δᶜ x q · 0b ∪ a) (ldef∅· {x}) ∙ rid ∙ def∅·) i
  δᶜ (dist {x} {y} {z} i) q = (cong (λ a → a ∪ ((δᶜ y q ∪ δᶜ z q) · x)) (dist {δᶜ x q} {y} {z})
      ∙ cong (λ a → (δᶜ x q · y ∪ δᶜ x q · z) ∪ a) (ldist {x} {δᶜ y q} {δᶜ z q}) ∙ assoc
      ∙ cong (λ a → (a ∪ δᶜ y q · x) ∪ δᶜ z q · x) comm
      ∙ cong (λ a → a ∪ δᶜ z q · x) (sym (assoc))
      ∙ cong (λ a → a ∪ δᶜ z q · x) comm
      ∙ sym assoc) i
  δᶜ (distƛ∪ {C} {x} {y} i) q = distƛ∪ {_} {λ z → δᶜ (x z) q} {λ z → δᶜ (y z) q} i
  δᶜ (distƛ· {C} {x} {y} i) q = (distƛ∪ {_} {(λ z → δᶜ (x z) q · y)} {λ z →  δᶜ y q · x z} ∙ cong₂ _∪_ distƛ· ldistƛ·) i
  δᶜ (remƛ {C} x i) q = remƛ {C} (δᶜ x q) i
  δᶜ (commƛ f i) q = commƛ (λ e v → δᶜ (f e v) q) i

  δᶜ-0b z = ElimProp.f (λ {z} x y i → squash (δᶜ z 0b) 0b x y i) refl refl (λ x y → refl)
                       (λ f fb → cong ƛ_ (funExt (λ x i → fb x i)) ∙ remƛ 0b ) (λ eq1 eq2 → cong₂ _∪_ eq1 eq2 ∙ rid)
                       (λ {x} {y} eq1 eq2 → cong₂ _∪_ (cong (_· y) eq1 ∙ comm· ∙ def∅·) (cong (_· x) eq2 ∙ comm· ∙ def∅·) ∙ rid) z

  δᶜ-1b z = ElimProp.f (λ {z} → squash (δᶜ z 1b) 0b) refl refl (λ x y → refl)
                       (λ f fb → cong ƛ_ (funExt (λ z i → fb z i)) ∙ remƛ 0b) (λ eq1 eq2 → cong₂ _∪_ eq1 eq2 ∙ rid)
                       (λ {x} {y} eq1 eq2 → cong₂ _∪_ (cong (_· y) eq1 ∙ comm· ∙ def∅·) (cong (_· x) eq2 ∙ comm· ∙ def∅·) ∙ rid) z

  δᶜ-comm x y = ElimProp.f (λ {z} → squash (δᶜ z y) (δᶜ y z)) (sym (δᶜ-0b y)) (sym (δᶜ-1b y)) l1 (λ f eq → cong ƛ_ (funExt eq) ∙ δᶜ-ƛ y f) (l2 y) (λ {x1} {y1} eq1 eq2 → cong₂ _∪_ (cong (_· y1) eq1) (cong (_· x1) eq2) ∙ l3 y) x where
    l1 : (x1 : C) → (y1 : D) → δᶜ (x1 ← y1) y ≡ δᶜ y (x1 ← y1)
    l1 x1 y1 = ElimProp.f (λ {z} → squash (δᶜ (x1 ← y1) z) (δᶜ z (x1 ← y1))) refl refl (λ x2 y2 → comm ∙ cong₂ _∪_ comm· comm·) (λ f eqf → cong ƛ_ (funExt eqf)) (λ eq1 eq2 → cong₂ _∪_ eq1 eq2) (λ eq1 eq2 → cong₂ _∪_ (cong (_· _) eq1) (cong (_· _) eq2)) y
    l2 : ∀ y → {z : Bree} {w : Bree} → δᶜ z y ≡ δᶜ y z → δᶜ w y ≡ δᶜ y w → δᶜ z y ∪ δᶜ w y ≡ δᶜ y (z ∪ w)
    l2 y {z} {w} eq1 eq2 = cong₂ _∪_ eq1 eq2 ∙ ElimProp.f (λ {e} → squash (δᶜ e z ∪ δᶜ e w) (δᶜ e (z ∪ w))) rid rid (λ _ _ → refl) (λ f eq → sym distƛ∪ ∙ cong ƛ_ (funExt eq)) (λ {x1} {y1} eq1 eq2 → assoc ∙ cong (_∪ δᶜ y1 w) (sym assoc ∙ cong (δᶜ x1 z ∪_) comm ∙ assoc) ∙ sym assoc ∙ cong₂ _∪_ eq1 eq2) (λ {x1} {y1} eq1 eq2 → assoc ∙ cong (_∪ δᶜ y1 w · x1) (sym assoc ∙ cong (δᶜ x1 z · y1 ∪_) comm ∙ assoc) ∙ sym assoc ∙ cong₂ _∪_ (sym ldist ∙ cong (_· _) eq1) (sym ldist ∙ cong (_· _) eq2)) y
    l3 : ∀ y → ∀{x1 y1} → δᶜ y x1 · y1 ∪ δᶜ y y1 · x1 ≡ δᶜ y (x1 · y1)
    l3 y {x1} {y1} = ElimProp.f (λ {z} → squash (δᶜ z x1 · y1 ∪ δᶜ z y1 · x1) (δᶜ z (x1 · y1)))
                                (cong₂ _∪_ ldef∅· ldef∅· ∙ rid)
                                (cong₂ _∪_ ldef∅· ldef∅· ∙ rid)
                                (λ _ _ → refl)
                                (λ f eq → cong₂ _∪_ (sym distƛ·) (sym distƛ·) ∙ sym distƛ∪ ∙ cong ƛ_ (funExt eq))
                                (λ {z} {w} eq1 eq2 → cong₂ _∪_ ldist ldist ∙ assoc ∙ cong (_∪ δᶜ w y1 · x1) (sym assoc ∙ (cong ( δᶜ z x1 · y1 ∪_) comm) ∙ assoc ∙ cong (_∪ δᶜ w x1 · y1) eq1) ∙ (sym assoc) ∙ cong (_ ∪_) eq2)
                                (λ {z} {w} eq1 eq2 →   cong₂ _∪_ ldist ldist ∙ assoc ∙ cong (_∪ (δᶜ w y1 · z) · x1) (sym assoc ∙ (cong ((δᶜ z x1 · w) · y1 ∪_) comm)
                                                     ∙ assoc ∙ cong ( _∪ (δᶜ w x1 · z) · y1) ((cong₂ _∪_ (sym assoc· ∙ cong  (δᶜ z x1 ·_) comm· ∙ assoc·) (sym assoc· ∙ cong  (δᶜ z y1 ·_) comm· ∙ assoc·) ∙ sym ldist)
                                                     ∙ cong (_· w) eq1)) ∙ sym assoc ∙ cong (δᶜ z (x1 · y1) · w ∪_) (cong₂ _∪_ (sym assoc· ∙ cong (δᶜ w x1 ·_) comm· ∙ assoc·) (sym assoc· ∙ cong (δᶜ w y1 ·_) comm· ∙ assoc·) ∙ sym ldist ∙ cong (_· z) eq2))
                                y



  δᶜ-permq x1 y1 x2 y2 q = ElimProp.f
    (λ {z} → squash (δᶜ (x1 ← y1) z · x2 ← y2 ∪ δᶜ (x2 ← y2) z · x1 ← y1) (δᶜ (x1 ← y2) z · x2 ← y1 ∪ δᶜ (x2 ← y1) z · x1 ← y2))
    (cong₂ _∪_ ldef∅· ldef∅· ∙ rid ∙ sym (cong₂ _∪_ ldef∅· ldef∅· ∙ rid))
    (cong₂ _∪_ ldef∅· ldef∅· ∙ rid ∙ sym (cong₂ _∪_ ldef∅· ldef∅· ∙ rid))
    (λ x y → cong₂ _∪_ (ldist ∙ cong₂ _∪_ (sym assoc· ∙ (cong (cm x1 y ·_) perm) ∙ assoc·)
                                          (sym assoc· ∙ thr· {c = cm x y1} (perm ∙ comm·) ∙ assoc·))
                       (ldist ∙ cong₂ _∪_ (sym assoc· ∙ (cong (cm x2 y ·_) perm) ∙ assoc·)
                                          (sym assoc· ∙ thr· (perm ∙ comm·) ∙ assoc·))
             ∙ assoc ∙ comm ∙ assoc ∙ cong (_∪ (cm x2 y · x ← y1) · x1 ← y2) (assoc ∙ cong (_∪ (x2 ← y · cm x y1) · x1 ← y2) (comm ∙ sym ldist))
             ∙ sym assoc ∙ cong (((cm x1 y · x ← y2 ∪ x1 ← y · cm x y2) · x2 ← y1) ∪_) (comm ∙ sym ldist))
    (λ f eq →   cong₂ _∪_ (sym distƛ·) (sym distƛ·) ∙ sym distƛ∪ ∙ cong ƛ_ (funExt eq)
              ∙ distƛ∪ ∙ cong₂ _∪_ distƛ· distƛ·)
    (λ {x} {y} eq1 eq2 →   cong₂ _∪_ ldist ldist ∙ assoc
                         ∙ cong (_∪ δᶜ (x2 ← y2) y · x1 ← y1) (comm ∙ assoc ∙ cong (_∪ δᶜ (x1 ← y1) y · x2 ← y2) (comm ∙ eq1)) ∙ sym assoc ∙ cong ((δᶜ (x1 ← y2) x · x2 ← y1 ∪ δᶜ (x2 ← y1) x · x1 ← y2) ∪_) eq2 ∙ assoc ∙ cong (_∪ δᶜ (x2 ← y1) y · x1 ← y2) (comm ∙ assoc ∙ cong (_∪ δᶜ (x2 ← y1) x · x1 ← y2) (comm ∙ sym ldist)) ∙ sym assoc ∙ cong ((δᶜ (x1 ← y2) x ∪ δᶜ (x1 ← y2) y) · x2 ← y1 ∪_) (sym ldist))
    (λ {x} {y} eq1 eq2 → cong₂ _∪_ (ldist ∙ cong₂ _∪_ (sym assoc· ∙ cong (δᶜ (x1 ← y1) x ·_) comm· ∙ assoc·)
                                                      (sym assoc· ∙ cong (δᶜ (x1 ← y1) y ·_) comm· ∙ assoc·))
                                   (ldist ∙  cong₂ _∪_ (sym assoc· ∙ cong (δᶜ (x2 ← y2) x ·_) comm· ∙ assoc·)
                                                      (sym assoc· ∙ cong (δᶜ (x2 ← y2) y ·_) comm· ∙ assoc·))
                         ∙ assoc ∙ cong (_∪ ((δᶜ (x2 ← y2) y · x1 ← y1) · x)) (comm ∙ assoc ∙ cong (_∪ (δᶜ (x1 ← y1) y · x2 ← y2) · x) (comm ∙ sym ldist ∙ cong (_· y) eq1 ∙ ldist ∙ cong₂ _∪_
                                                                   (sym assoc· ∙ cong (δᶜ (x1 ← y2) x ·_) comm· ∙ assoc·)
                                                                   (sym assoc· ∙ cong (δᶜ (x2 ← y1) x ·_) comm· ∙ assoc·) )) ∙ sym assoc
         ∙ cong (((δᶜ (x1 ← y2) x · y) · x2 ← y1 ∪ (δᶜ (x2 ← y1) x · y) · x1 ← y2) ∪_)
              (sym ldist ∙ cong (_· x) eq2 ∙ ldist ∙ cong₂ _∪_ (sym assoc· ∙ cong (δᶜ (x1 ← y2) y ·_) comm· ∙ assoc·) (sym assoc· ∙ cong (δᶜ (x2 ← y1) y ·_) comm· ∙ assoc·))
         ∙ assoc ∙ cong (_∪ (δᶜ (x2 ← y1) y · x) · x1 ← y2) (comm ∙ assoc ∙ cong (_∪ (δᶜ (x2 ← y1) x · y) · x1 ← y2) (comm ∙ sym ldist)) ∙ sym assoc ∙ cong ((δᶜ (x1 ← y2) x · y ∪ δᶜ (x1 ← y2) y · x) · x2 ← y1 ∪_) (sym ldist))
   
    q


  δᶜ-ƛ y f = ElimProp.f (λ {z} → squash ((ƛ (λ d → δᶜ z (f d)))) (δᶜ z (ƛ f))) (remƛ 0b) (remƛ 0b) (λ x y₁ → refl)
                        (λ g eq → commƛ (λ x y → δᶜ (g y) (f x)) ∙ (cong ƛ_ (funExt eq)))
                        (λ eq1 eq2 → distƛ∪ ∙ cong₂ _∪_ eq1 eq2)
                        (λ {x} {y} eq1 eq2 → distƛ∪ ∙ cong₂ _∪_ (distƛ· ∙ cong (_· y) eq1) (distƛ· ∙ cong (_· x) eq2))
                        y




  δᶜ-permq2 x1 y1 x2 y2 0b = cong₂ _∪_ ldef∅· ldef∅· ∙ rid ∙ sym (cong₂ _∪_ ldef∅· ldef∅· ∙ rid)
  δᶜ-permq2 x1 y1 x2 y2 1b = cong₂ _∪_ ldef∅· ldef∅· ∙ rid ∙ sym (cong₂ _∪_ ldef∅· ldef∅· ∙ rid)
  δᶜ-permq2 x1 y1 x2 y2 (x ← y) = cong₂ _∪_ (ldist ∙ cong₂ _∪_ (sym assoc· ∙ (cong (cm x1 y ·_) perm) ∙ assoc·)
                                          (sym assoc· ∙ thr· {c = cm x y1} (perm ∙ comm·) ∙ assoc·))
                       (ldist ∙ cong₂ _∪_ (sym assoc· ∙ (cong (cm x2 y ·_) perm) ∙ assoc·)
                                          (sym assoc· ∙ thr· (perm ∙ comm·) ∙ assoc·))
             ∙ assoc ∙ comm ∙ assoc ∙ cong (_∪ (cm x2 y · x ← y1) · x1 ← y2) (assoc ∙ cong (_∪ (x2 ← y · cm x y1) · x1 ← y2) (comm ∙ sym ldist))
             ∙ sym assoc ∙ cong (((cm x1 y · x ← y2 ∪ x1 ← y · cm x y2) · x2 ← y1) ∪_) (comm ∙ sym ldist)
  δᶜ-permq2 x1 y1 x2 y2 (ƛ f) = cong₂ _∪_ (sym distƛ·) (sym distƛ·) ∙ sym distƛ∪ ∙ cong ƛ_ (funExt λ z → δᶜ-permq2 x1 y1 x2 y2 (f z))
              ∙ distƛ∪ ∙ cong₂ _∪_ distƛ· distƛ·
  δᶜ-permq2 x1 y1 x2 y2 (x ∪ y) = cong₂ _∪_ ldist ldist ∙ assoc
                         ∙ cong (_∪ δᶜ (x2 ← y2) y · x1 ← y1) (comm ∙ assoc ∙ cong (_∪ δᶜ (x1 ← y1) y · x2 ← y2) (comm ∙ δᶜ-permq2 x1 y1 x2 y2 x)) ∙ sym assoc ∙ cong ((δᶜ (x1 ← y2) x · x2 ← y1 ∪ δᶜ (x2 ← y1) x · x1 ← y2) ∪_) (δᶜ-permq2 x1 y1 x2 y2 y) ∙ assoc ∙ cong (_∪ δᶜ (x2 ← y1) y · x1 ← y2) (comm ∙ assoc ∙ cong (_∪ δᶜ (x2 ← y1) x · x1 ← y2) (comm ∙ sym ldist)) ∙ sym assoc ∙ cong ((δᶜ (x1 ← y2) x ∪ δᶜ (x1 ← y2) y) · x2 ← y1 ∪_) (sym ldist)
  δᶜ-permq2 x1 y1 x2 y2 (x · y) = cong₂ _∪_ (ldist ∙ cong₂ _∪_ (sym assoc· ∙ cong (δᶜ (x1 ← y1) x ·_) comm· ∙ assoc·)
                                                      (sym assoc· ∙ cong (δᶜ (x1 ← y1) y ·_) comm· ∙ assoc·))
                                   (ldist ∙  cong₂ _∪_ (sym assoc· ∙ cong (δᶜ (x2 ← y2) x ·_) comm· ∙ assoc·)
                                                      (sym assoc· ∙ cong (δᶜ (x2 ← y2) y ·_) comm· ∙ assoc·))
                         ∙ assoc ∙ cong (_∪ ((δᶜ (x2 ← y2) y · x1 ← y1) · x)) (comm ∙ assoc ∙ cong (_∪ (δᶜ (x1 ← y1) y · x2 ← y2) · x) (comm ∙ sym ldist ∙ cong (_· y) (δᶜ-permq2 x1 y1 x2 y2 x) ∙ ldist ∙ cong₂ _∪_
                                                                   (sym assoc· ∙ cong (δᶜ (x1 ← y2) x ·_) comm· ∙ assoc·)
                                                                   (sym assoc· ∙ cong (δᶜ (x2 ← y1) x ·_) comm· ∙ assoc·) )) ∙ sym assoc
         ∙ cong (((δᶜ (x1 ← y2) x · y) · x2 ← y1 ∪ (δᶜ (x2 ← y1) x · y) · x1 ← y2) ∪_)
              (sym ldist ∙ cong (_· x) (δᶜ-permq2 x1 y1 x2 y2 y) ∙ ldist ∙ cong₂ _∪_ (sym assoc· ∙ cong (δᶜ (x1 ← y2) y ·_) comm· ∙ assoc·) (sym assoc· ∙ cong (δᶜ (x2 ← y1) y ·_) comm· ∙ assoc·))
         ∙ assoc ∙ cong (_∪ (δᶜ (x2 ← y1) y · x) · x1 ← y2) (comm ∙ assoc ∙ cong (_∪ (δᶜ (x2 ← y1) x · y) · x1 ← y2) (comm ∙ sym ldist)) ∙ sym assoc ∙ cong ((δᶜ (x1 ← y2) x · y ∪ δᶜ (x1 ← y2) y · x) · x2 ← y1 ∪_) (sym ldist)
  δᶜ-permq2 x1 y1 x2 y2 (squash a b p1 p2 i j) = {!squash!}
  δᶜ-permq2 x1 y1 x2 y2 (assoc i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (rid i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (comm i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (idem i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (perm i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (assoc· i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (rid· i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (comm· i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (def∅· i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (dist i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (distƛ∪ i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (distƛ· i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (remƛ q i) = {!!}
  δᶜ-permq2 x1 y1 x2 y2 (commƛ f i) = {!!}







  δ  : Bree → Bree
  δᵃ : Bree → Bree → Bree
  δᵃ-comm : (x y : Bree) → δᵃ x y ≡ δᵃ y x
  δᵃ-linr : ∀ x y z → δᵃ x (y ∪ z) ≡ δᵃ x y ∪ δᵃ x z
  δ-dist : ∀ x y z → δ (x · (y ∪ z)) ≡ δ (x · y) ∪ δ (x · z)

  δᵃ-linr x y z = cong (δ x · (y ∪ z) ∪_) dist ∙ cong (_∪ x · δ y ∪ x · δ z) dist ∙ assoc ∙ cong (_∪ (x · δ z)) (sym assoc ∙ cong (δ x · y ∪_) comm ∙ assoc) ∙ sym assoc
 
  δ-dist x y z = cong₂ _∪_ (δᵃ-linr x y z) (δᶜ-linr x y z) ∙ assoc ∙ cong (_∪ δᶜ x z) (sym assoc ∙ cong (δᵃ x y ∪_) comm ∙ assoc) ∙ sym assoc

  δ 0b = 0b
  δ 1b = 0b
  δ (x ← y) = cm x y
  δ (ƛ x) = ƛ λ z → δ (x z)
  δ (x ∪ y) = δ x ∪ δ y
  δ (x · y) = δᵃ x y ∪ δᶜ x y
  δ (squash a b p1 p2 i j) = isOfHLevel→isOfHLevelDep 2 (λ x → squash)  (δ a) (δ b) (cong δ p1) (cong δ p2) (squash a b p1 p2) i j
  δ (assoc {x} {y} {z} i) = assoc {δ x} {δ y} {δ z} i
  δ (rid {b} i) = rid {δ b} i
  δ (comm {x} {y} i) = comm {δ x} {δ y} i
  δ(idem {x} i) = idem {δ x} i
  δ (perm {x1} {y1} {x2} {y2} i) = comm {cm x1 y1 · x2 ← y2 ∪ x1 ← y1 · cm x2 y2} {cm x1 y2 · x2 ← y1 ∪ x1 ← y2 · cm x2 y1} i
  δ (assoc· {x} {y} {z} i) = (cong ((δ x · y · z ∪ x · ((δ y · z ∪ y · δ z) ∪ δᶜ y z)) ∪_) (δᶜ-comm x (y · z))
    ∙ cong (_∪ (δᶜ y x · z ∪ δᶜ z x · y)) (cong (δ x · y · z ∪_) (dist ∙ cong (_∪ x · δᶜ y z) (dist ∙ cong (x · δ y · z ∪_) assoc·) ∙ cong ((x · δ y · z ∪ (x · y) · δ z) ∪_) comm·)) ∙ assoc
    ∙ cong (_∪ δᶜ z x · y) (sym assoc ∙ cong (δ x · y · z ∪_) (sym assoc ∙ cong ((x · δ y · z ∪ (x · y) · δ z) ∪_) comm ∙ assoc) ∙  assoc ∙ cong (_∪ δᶜ y z · x) ((cong (δ x · y · z ∪_) (sym assoc ∙ cong (x · δ y · z ∪_) comm ∙ assoc) ∙ assoc ∙ cong (_∪ (x · y) · δ z) (assoc ∙ cong (_∪ δᶜ y x · z) (cong₂ _∪_ assoc· assoc· ∙ sym ldist)
    ∙ cong (λ q → (δ x · y ∪ x · δ y) · z ∪ q · z) (δᶜ-comm y x) ∙ sym ldist)))) ∙ sym assoc
    ∙ cong ((((δ x · y ∪ x · δ y) ∪ δᶜ x y) · z ∪ (x · y) · δ z) ∪_) (comm ∙ cong (_∪ (δᶜ y z · x)) (cong (_· y) (δᶜ-comm z x)))) i
  δ (rid· {x} i) = (cong (_∪ δᶜ x 1b) (cong₂ _∪_ (rid· {δ x}) (def∅· {x}) ∙ rid {δ x}) ∙ cong (δ x ∪_) (δᶜ-comm x 1b) ∙ rid {δ x}) i
  δ (comm· {x} {y} i) = cong₂ _∪_ (δᵃ-comm x y) (δᶜ-comm x y) i
  δ (def∅· {x} i) = (cong₂ _∪_ (cong₂ _∪_ (def∅· {δ x}) (def∅· {x}) ∙ rid) (δᶜ-comm x 0b) ∙ rid) i
  δ (dist {x} {y} {z} i) = (cong₂ _∪_ ( cong (δ x · (y ∪ z) ∪_) dist ∙ cong (_∪ x · δ y ∪ x · δ z) dist ∙ assoc ∙ cong (_∪ (x · δ z)) (sym assoc ∙ cong (δ x · y ∪_) comm ∙ assoc) ∙ sym assoc) (δᶜ-linr x y z) ∙ assoc ∙ cong (_∪ δᶜ x z) (sym assoc ∙ cong (δᵃ x y ∪_) comm ∙ assoc) ∙ sym assoc) i
  
  δ (distƛ∪ {C} {x} {y} i) = distƛ∪ {C} {λ z → δ (x z)} {λ z → δ (y z)} i
  δ (distƛ· {C} {x} {y} i) = (distƛ∪ {x = λ z → δ (x z) · y ∪ x z · δ y} {y = λ z → δᶜ (x z) y} ∙ cong (_∪ (ƛ (λ z → δᶜ (x z) y))) (distƛ∪ ∙ cong₂ _∪_ distƛ· distƛ·)) i
  δ (remƛ {C} x i) = remƛ {C} (δ x) i
  δ (commƛ f i) = commƛ (λ e v → δ (f e v)) i

  δᵃ x y = (δ x ·  y) ∪ (x · δ y)

  δᵃ-comm x y = comm ∙ cong₂ (λ a b → a ∪ b) comm· comm·
  
  data P {ℓ} (Q : Set ℓ) : Set ℓ where
    onel : Q → P Q
    oner : Q → P Q

  module D = MBree {_} {_} {P C} {P D}

  lifl : Bree → D.Bree
  lifl 0b = D.0b
  lifl 1b = D.1b
  lifl (x ← x₁) = D._←_ (onel x) (onel x₁)
  lifl (ƛ f) = D.ƛ_ λ z → lifl (f z)
  lifl (x1 ∪ x2) = D._∪_ (lifl x1) (lifl x2)
  lifl (x1 · x2) = D._·_ (lifl x1) (lifl x2)
  lifl (squash a b p1 p2 i j) = D.squash (lifl a) (lifl b) (cong lifl p1) (cong lifl p2) i j
  lifl (assoc {a} {b} {c} i) = D.assoc {lifl a} {lifl b} {lifl c} i 
  lifl (rid {x} i) = D.rid {lifl x} i
  lifl (comm {x} {y} i) = D.comm {lifl x} {lifl y} i
  lifl (idem {x} i) = D.idem {lifl x} i
  lifl (perm {x1} {y1} {x2} {y2} i) = D.perm {onel x1} {onel y1} {onel x2} {onel y2} i
  lifl (assoc· {x} {y} {z} i) = D.assoc· {lifl x} {lifl y} {lifl z} i
  lifl (rid· {x} i) = D.rid· {lifl x} i
  lifl (comm· {a} {b} i) = D.comm· {lifl a} {lifl b} i
  lifl (def∅· {x} i) = D.def∅· {lifl x} i
  lifl (dist {x} {y} {z} i) = D.dist {lifl x} {lifl y} {lifl z} i
  lifl (distƛ∪ {_} {x} {y} i) = D.distƛ∪ {_} {λ z → lifl (x z)} {λ z → lifl (y z)} i
  lifl (distƛ· {_} {x} {y} i) = D.distƛ· {_} {λ z → lifl (x z)} {lifl y} i
  lifl (remƛ {C} x i) = D.remƛ {C} (lifl x) i
  lifl (commƛ f i) = D.commƛ (λ x y → lifl (f x y)) i

  lifr : Bree → D.Bree
  lifr 0b = D.0b
  lifr 1b = D.1b
  lifr (x ← x₁) = D._←_ (oner x) (oner x₁)
  lifr (ƛ f) = D.ƛ_ λ z → lifr (f z)
  lifr (x1 ∪ x2) = D._∪_ (lifr x1) (lifr x2)
  lifr (x1 · x2) = D._·_ (lifr x1) (lifr x2)
  lifr (squash a b p1 p2 i j) = D.squash (lifr a) (lifr b) (cong lifr p1) (cong lifr p2) i j
  lifr (assoc {a} {b} {c} i) = D.assoc {lifr a} {lifr b} {lifr c} i 
  lifr (rid {x} i) = D.rid {lifr x} i
  lifr (comm {x} {y} i) = D.comm {lifr x} {lifr y} i
  lifr (idem {x} i) = D.idem {lifr x} i
  lifr (perm {x1} {y1} {x2} {y2} i) = D.perm {oner x1} {oner y1} {oner x2} {oner y2} i
  lifr (assoc· {x} {y} {z} i) = D.assoc· {lifr x} {lifr y} {lifr z} i
  lifr (rid· {x} i) = D.rid· {lifr x} i
  lifr (comm· {a} {b} i) = D.comm· {lifr a} {lifr b} i
  lifr (def∅· {x} i) = D.def∅· {lifr x} i
  lifr (dist {x} {y} {z} i) = D.dist {lifr x} {lifr y} {lifr z} i
  lifr (distƛ∪ {_} {x} {y} i) = D.distƛ∪ {_} {λ z → lifr (x z)} {λ z → lifr (y z)} i
  lifr (distƛ· {_} {x} {y} i) = D.distƛ· {_} {λ z → lifr (x z)} {lifr y} i
  lifr (remƛ {C} x i) = D.remƛ {C} (lifr x) i
  lifr (commƛ f i) = D.commƛ (λ x y → lifr (f x y)) i

  tetr : P C → P D → Bool
  tetr (onel a) (onel b) = true
  tetr (onel a) (oner b) with decm a b
  ... | yes _ = true
  ... | no _ = false
  tetr (oner a) (onel b) with decm a b
  ... | yes _ = true
  ... | no _ = false
  tetr (oner a) (oner b) = true
  

  {-# TERMINATING #-}
  zerod : D.Bree → D.Bree → D.Bree
  zerod 0b y = D.0b
  zerod 1b y = y
  zerod (ƛ f) y = D.ƛ λ z → zerod (f z) y
  zerod (x1 ∪ x2) y = zerod x1 y D.∪ zerod x2 y
  zerod (x1 · x2) y = zerod x2 (zerod x1 y)
  zerod (a ← b) 0b = D.0b
  zerod x@(a ← b) 1b = x
  zerod s@(z ← q) a@(w ← e) with tetr w q
  ... | false = D.0b
  ... | true with tetr z e
  ... | true = s D.· a
  ... | false = D.0b
  zerod x@(a ← b) (ƛ f) = D.ƛ λ z → zerod x (f z)
  zerod x@(a ← b) (y1 ∪ y2) = zerod x y1 D.∪ zerod x y2 
  zerod x@(_ ← _) (y1 · y2) = zerod (zerod x y1) y2 
  zerod x@(_ ← _) (squash a b p1 p2 i j) = D.squash (zerod x a) (zerod x b) (λ i → zerod x (p1 i)) (λ i → zerod x (p2 i)) i j
  zerod x@(_ ← _) (assoc {y} {z} {w} i) = D.assoc {zerod x y} {zerod x z} {zerod x w} i
  zerod x@(_ ← _) (rid {y} i) = D.rid {zerod x y} i
  zerod x@(_ ← _) (comm {y} {z} i) = D.comm {zerod x y} {zerod x z} i
  zerod x@(_ ← _) (idem {y} i) = D.idem {zerod x y} i
  zerod (x3 ← y3) (perm {x1} {y1} {x2} {y2} i) with tetr x1 y3
  ... | false = refl i
  zerod (onel x MBree.← y3) (MBree.perm {x1} {onel x₁} {x2} {onel x₂} i) | true with tetr x2 y3
  ... | false = refl i
  ... | true with tetr x1 y3
  ... | true = {!!}
  zerod (onel x MBree.← y3) (MBree.perm {x1} {onel x₁} {x2} {oner x₂} i) | true = {!!}
  zerod (onel x MBree.← y3) (MBree.perm {x1} {oner x₁} {x2} {y2} i) | true = {!!}
  zerod (oner x MBree.← y3) (MBree.perm {x1} {y1} {x2} {y2} i) | true = {!!}
  zerod x@(_ ← _) (assoc· {y} {z} {w} i) = {!!}
  zerod x@(_ ← _) (rid· i) = {!!}
  zerod x@(_ ← _) (comm· i) = {!!}
  zerod x@(_ ← _) (def∅· i) = {!!}
  zerod x@(_ ← _) (dist i) = {!!}
  zerod x@(_ ← _) (distƛ∪ i) = {!!}
  zerod x@(_ ← _) (distƛ· i) = {!!}
  zerod x@(_ ← _) (remƛ y i) = {!!}
  zerod x@(_ ← _) (commƛ f i) = {!!}
  zerod (squash x x₁ x₂ y₁ i i₁) y = {!!}
  zerod (assoc i) y = {!!}
  zerod (rid i) y = {!!}
  zerod (comm i) y = {!!}
  zerod (idem i) y = {!!}
  zerod (perm i) y = {!!}
  zerod (assoc· i) y = {!!}
  zerod (rid· i) y = {!!}
  zerod (comm· i) y = {!!}
  zerod (def∅· i) y = {!!}
  zerod (dist i) y = {!!}
  zerod (distƛ∪ i) y = {!!}
  zerod (distƛ· i) y = {!!}
  zerod (remƛ x i) y = {!!}
  zerod (commƛ f i) y = {!!}
  
  zeroᶜ : Bree → Bree → MBree.Bree
  zeroᶜ 0b y = 0b
  zeroᶜ 1b y = y
  zeroᶜ (ƛ f) y = ƛ λ z → zeroᶜ (f z) y 
  zeroᶜ (x1 ∪ x2) y = zeroᶜ x1 y ∪ zeroᶜ x2 y
  zeroᶜ (x1 · x2) y = {!!} -- zeroᶜ (zeroᶜ x1 y) x2
  zeroᶜ (z ← q) 0b = 0b
  zeroᶜ x@(_ ← _) 1b = x
  zeroᶜ q@(x1 ← y1) z@(x2 ← y2) with decm x1 y2 | decm x2 y1
  ... | yes _ | yes _ = q · z
  ... | r1 | r2 = {!!}
  zeroᶜ (z ← q) (ƛ x) = {!!}
  zeroᶜ (z ← q) (y ∪ y₁) = {!!}
  zeroᶜ (z ← q) (y · y₁) = {!!}
  zeroᶜ (z ← q) (squash y y₁ x y₂ i i₁) = {!!}
  zeroᶜ (z ← q) (assoc i) = {!!}
  zeroᶜ (z ← q) (rid i) = {!!}
  zeroᶜ (z ← q) (comm i) = {!!}
  zeroᶜ (z ← q) (idem i) = {!!}
  zeroᶜ (z ← q) (perm i) = {!!}
  zeroᶜ (z ← q) (assoc· i) = {!!}
  zeroᶜ (z ← q) (rid· i) = {!!}
  zeroᶜ (z ← q) (comm· i) = {!!}
  zeroᶜ (z ← q) (def∅· i) = {!!}
  zeroᶜ (z ← q) (dist i) = {!!}
  zeroᶜ (z ← q) (distƛ∪ i) = {!!}
  zeroᶜ (z ← q) (distƛ· i) = {!!}
  zeroᶜ (z ← q) (remƛ y i) = {!!}
  zeroᶜ (z ← q) (commƛ f i) = {!!}
  zeroᶜ (squash x x₁ x₂ y₁ i i₁) y = {!!}
  zeroᶜ (assoc i) y = {!!}
  zeroᶜ (rid i) y = {!!}
  zeroᶜ (comm i) y = {!!}
  zeroᶜ (idem i) y = {!!}
  zeroᶜ (perm i) y = {!!}
  zeroᶜ (assoc· i) y = {!!}
  zeroᶜ (rid· i) y = {!!}
  zeroᶜ (comm· i) y = {!!}
  zeroᶜ (def∅· i) y = {!!}
  zeroᶜ (dist i) y = {!!}
  zeroᶜ (distƛ∪ i) y = {!!}
  zeroᶜ (distƛ· i) y = {!!}
  zeroᶜ (remƛ x i) y = {!!}
  zeroᶜ (commƛ f i) y = {!!}
  
  zero : Bree → Bree
  zero 0b = 0b
  zero 1b = 1b
  zero x@(a ← b) with decm a b
  ... | yes p = x
  ... | no ¬p = 0b
  zero (ƛ f) = ƛ λ c → zero (f c)
  zero (x ∪ y) = zero x ∪ zero y
  zero (x · y) = zero x · zero y
  zero (squash a b p1 p2 i j) =  isOfHLevel→isOfHLevelDep 2 (λ x → squash)  (zero a) (zero b) (cong zero p1) (cong zero p2) (squash a b p1 p2) i j
  zero (assoc {x} {y} {z} i) = assoc {zero x} {zero y} {zero z} i
  zero (rid {x} i) = rid {zero x} i
  zero (comm {x} {y} i) = comm {zero x} {zero y} i
  zero (idem {x} i) = {!idem {zero x} i!}
  zero (perm i) = {!!}
  zero (assoc· i) = {!!}
  zero (rid· i) = {!!}
  zero (comm· i) = {!!}
  zero (def∅· i) = {!!}
  zero (dist i) = {!!}
  zero (distƛ∪ i) = {!!}
  zero (distƛ· i) = {!!}
  zero (remƛ x i) = {!!}
  zero (commƛ f i) = {!!}
