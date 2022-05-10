{-# OPTIONS --sized-types --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid

import MBree
open import SemiRing

module MDerivation {ℓ ℓ'} (C : Type ℓ) (D : Type ℓ') where

open MBree {_} {_} {C} {D}

module Derivation (cm : C → D → Bree) where

  open SemiRingStr (snd BreeSemiRing)

  δ  : Bree → Bree
  δᵃ : Bree → Bree → Bree
  δᶜ : Bree → Bree → Bree
  δᵃ-comm : (x y : Bree) → δᵃ x y ≡ δᵃ y x
  δᶜ-0b : (x : Bree) → δᶜ x 0b ≡ 0b
  δᶜ-1b : (x : Bree) → δᶜ x 1b ≡ 0b
  δᶜ-comm : (x y : Bree) → δᶜ x y ≡ δᶜ y x
  δᶜ-ƛ : ∀ y → {B` : Type} (f : B` → Bree) →
         (ƛ (λ z → δᶜ y (f z))) ≡ δᶜ y (ƛ f)
  δᵃ-assocr : ∀ x y z → δᵃ x (y ∪ z) ≡ δᵃ x y ∪ δᵃ x z
  δᶜ-assocr : ∀ x y z → δᶜ x (y ∪ z) ≡ δᶜ x y ∪ δᶜ x z
  δ-assoc   : ∀ x y z → δ (x · (y ∪ z)) ≡ δ (x · y) ∪ δ (x · z)

  δᵃ-assocr x y z = cong (δ x · (y ∪ z) ∪_) dist ∙ cong (_∪ x · δ y ∪ x · δ z) dist ∙ assoc ∙ cong (_∪ (x · δ z)) (sym assoc ∙ cong (δ x · y ∪_) comm ∙ assoc) ∙ sym assoc
  
  δᶜ-assocr x y z = δᶜ-comm x (y ∪ z) ∙ cong₂ _∪_ (δᶜ-comm y x) (δᶜ-comm z x)

  δ-assoc x y z = cong₂ _∪_ (δᵃ-assocr x y z) (δᶜ-assocr x y z) ∙ assoc ∙ cong (_∪ δᶜ x z) (sym assoc ∙ cong (δᵃ x y ∪_) comm ∙ assoc) ∙ sym assoc

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
  δ (assoc· {x} {y} {z} i) = {!!}
  δ (rid· {x} i) = (cong (_∪ δᶜ x 1b) (cong₂ _∪_ (rid· {δ x}) (def∅· {x}) ∙ rid {δ x}) ∙ cong (δ x ∪_) (δᶜ-comm x 1b) ∙ rid {δ x}) i
  δ (comm· {x} {y} i) = cong₂ _∪_ (δᵃ-comm x y) (δᶜ-comm x y) i
  δ (def∅· {x} i) = (cong₂ _∪_ (cong₂ _∪_ (def∅· {δ x}) (def∅· {x}) ∙ rid) (δᶜ-comm x 0b) ∙ rid) i
-- i = i0 ⊢ δᵃ x (y ∪ z) ∪ δᶜ x (y ∪ z)
-- i = i1 ⊢ (δᵃ x y ∪ δᶜ x y) ∪ δᵃ x z ∪ δᶜ x z
  δ (dist {x} {y} {z} i) = {!!} -- δ-assoc x y z i
  δ (distƛ∪ {C} {x} {y} i) = distƛ∪ {C} {λ z → δ (x z)} {λ z → δ (y z)} i
-- i = i0 ⊢ ƛ (λ z → (δ (x z) · y z ∪ x z · δ (y z)) ∪ δᶜ (x z) (y z))
-- i = i1 ⊢ ((ƛ (λ z → δ (x z))) · (ƛ y) ∪
--           (ƛ x) · (ƛ (λ z → δ (y z))))
--          ∪ (ƛ (λ z → δᶜ (x z) (ƛ y)))

  δ (distƛ· {C} {x} {y} i) = {!!} -- (distƛ∪ {x = λ z → δ (x z) · y z ∪ x z · δ (y z)} {y = λ z → δᶜ (x z) (y z)} ∙ cong (_∪ (ƛ (λ z → δᶜ (x z) (y z)))) (distƛ∪ ∙ cong₂ _∪_ distƛ· distƛ·) ∙ {!!}) i
  δ (remƛ x f eq i) = remƛ (δ x) (λ e → δ (f e)) (λ z → cong δ (eq z)) i
  δ (commƛ f i) = commƛ (λ e v → δ (f e v)) i

  δᵃ x y = (δ x ·  y) ∪ (x · δ y)

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
  δᶜ q@(q1 ← w1) (perm {x1} {y1} {x2} {y2} i) = l1 i where
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
  δᶜ q@(_ ← _) (distƛ· {C} {x} {y} i) = (distƛ∪ {_} {λ z → δᶜ q (x z) · y z} {λ z → δᶜ q (y z) · x z}
      ∙ cong (λ a → ƛ (λ z → δᶜ q (x z) · y z) ∪ a) distƛ· ∙ cong (λ a → a ∪ ƛ (λ z → δᶜ q (y z)) · ƛ x) distƛ·) i
  δᶜ q@(_ ← _) (remƛ x y eq i) =  remƛ (δᶜ q x) (λ z → δᶜ q (y z)) (λ z → cong (λ a → δᶜ q a) (eq z)) i
  δᶜ q@(_ ← _) (commƛ f i) = commƛ (λ e v → δᶜ q (f e v)) i
  δᶜ (squash a b p1 p2 i j) y = isOfHLevel→isOfHLevelDep 2 (λ x → squash)  (δᶜ a y) (δᶜ b y) (cong (λ z → δᶜ z y) p1) (cong (λ z → δᶜ z y) p2) (squash a b p1 p2) i j
  δᶜ (assoc {x} {y} {z} i) q = assoc {δᶜ x q} {δᶜ y q} {δᶜ z q} i
  δᶜ (rid {x} i) q = rid {δᶜ x q} i
  δᶜ (comm {x} {y} i) q = comm {δᶜ x q} {δᶜ y q} i
  δᶜ (idem {x} i) q = idem {δᶜ x q} i
  δᶜ (perm {x1} {y1} {x2} {y2} i) q = {!!} -- ElimProp.f (λ {z} → squash (δᶜ (x1 ← y1) z · x2 ← y2 ∪ δᶜ (x2 ← y2) z · x1 ← y1) (δᶜ (x1 ← y2) z · x2 ← y1 ∪ δᶜ (x2 ← y1) z · x1 ← y2)) {!!} {!!} {!!} {!!} {!!} {!!} {!!} i
--  i = i0 ⊢ δᶜ (x1 ← y1) q · x2 ← y2 ∪ δᶜ (x2 ← y2) q · x1 ← y1
--  i = i1 ⊢ δᶜ (x1 ← y2) q · x2 ← y1 ∪ δᶜ (x2 ← y1) q · x1 ← y2
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
  δᶜ (distƛ· {C} {x} {y} i) q = (distƛ∪ {_} {(λ z → δᶜ (x z) q · y z)} {λ z →  δᶜ (y z) q · x z}
      ∙ cong (λ a → ƛ (λ z → δᶜ (x z) q · y z) ∪ a) distƛ· ∙ cong (λ a → a ∪ ƛ (λ z → δᶜ (y z) q) · ƛ x) distƛ·) i
  δᶜ (remƛ x y eq i) q = remƛ (δᶜ x q) (λ z → δᶜ (y z) q) (λ z → cong (λ a → δᶜ a q) (eq z)) i
  δᶜ (commƛ f i) q = commƛ (λ e v → δᶜ (f e v) q) i

  δᶜ-0b z = ElimProp.f (λ {z} x y i → squash (δᶜ z 0b) 0b x y i) refl refl (λ x y → refl)
                       (λ f eq → remƛ 0b (λ e → δᶜ (f e) 0b ) eq) (λ eq1 eq2 → cong₂ _∪_ eq1 eq2 ∙ rid)
                       (λ {x} {y} eq1 eq2 → cong₂ _∪_ (cong (_· y) eq1 ∙ comm· ∙ def∅·) (cong (_· x) eq2 ∙ comm· ∙ def∅·) ∙ rid) z

  δᶜ-1b z = ElimProp.f (λ {z} → squash (δᶜ z 1b) 0b) refl refl (λ x y → refl)
                       (λ f eq → remƛ 0b (λ e → δᶜ (f e) 1b ) eq) (λ eq1 eq2 → cong₂ _∪_ eq1 eq2 ∙ rid)
                       (λ {x} {y} eq1 eq2 → cong₂ _∪_ (cong (_· y) eq1 ∙ comm· ∙ def∅·) (cong (_· x) eq2 ∙ comm· ∙ def∅·) ∙ rid) z

  δᵃ-comm x y = comm ∙ cong₂ (λ a b → a ∪ b) comm· comm·

  δᶜ-ƛ y f = ElimProp.f (λ {z} → squash ((ƛ (λ d → δᶜ z (f d)))) (δᶜ z (ƛ f))) (remƛ 0b (λ x → 0b) (λ z → refl)) ((remƛ 0b (λ x → 0b) (λ z → refl))) (λ x y₁ → refl)
                        (λ g eq → commƛ (λ x y → δᶜ (g y) (f x)) ∙ (cong ƛ_ (funExt eq)))
                        (λ eq1 eq2 → distƛ∪ ∙ cong₂ _∪_ eq1 eq2)
                        (λ eq1 eq2 → distƛ∪ ∙ cong₂ _∪_ (distƛ· ∙ cong₂ _·_ eq1 (remƛ _ _ (λ z → refl))) (distƛ· ∙ cong₂ _·_ eq2 (remƛ _ _ (λ z → refl))))
                        y

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
                                (λ f eq → cong₂ _∪_ (cong ((ƛ (λ z → δᶜ (f z) x1)) ·_) (sym (remƛ y1 (λ e → y1) λ z → refl)) ∙ sym distƛ· ) (cong ((ƛ (λ z → δᶜ (f z) y1)) ·_) (sym (remƛ x1 (λ e → x1) λ z → refl)) ∙ sym distƛ·) ∙ sym distƛ∪ ∙ cong ƛ_ (funExt eq))
                                (λ {z} {w} eq1 eq2 → cong₂ _∪_ ldist ldist ∙ assoc ∙ cong (_∪ δᶜ w y1 · x1) (sym assoc ∙ (cong ( δᶜ z x1 · y1 ∪_) comm) ∙ assoc ∙ cong (_∪ δᶜ w x1 · y1) eq1) ∙ (sym assoc) ∙ cong (_ ∪_) eq2)
                                (λ {z} {w} eq1 eq2 →   cong₂ _∪_ ldist ldist ∙ assoc ∙ cong (_∪ (δᶜ w y1 · z) · x1) (sym assoc ∙ (cong ((δᶜ z x1 · w) · y1 ∪_) comm)
                                                     ∙ assoc ∙ cong ( _∪ (δᶜ w x1 · z) · y1) ((cong₂ _∪_ (sym assoc· ∙ cong  (δᶜ z x1 ·_) comm· ∙ assoc·) (sym assoc· ∙ cong  (δᶜ z y1 ·_) comm· ∙ assoc·) ∙ sym ldist)
                                                     ∙ cong (_· w) eq1)) ∙ sym assoc ∙ cong (δᶜ z (x1 · y1) · w ∪_) (cong₂ _∪_ (sym assoc· ∙ cong (δᶜ w x1 ·_) comm· ∙ assoc·) (sym assoc· ∙ cong (δᶜ w y1 ·_) comm· ∙ assoc·) ∙ sym ldist ∙ cong (_· z) eq2))
                                y
