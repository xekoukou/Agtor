{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import SemiRing

module Poly {ℓ ℓ'} (C : Type ℓ) (D : Type ℓ') where

infixr 5 _∪_
infixr 7 _·_
infixr 10 _←_

data Poly : Type (ℓ-max (ℓ-suc ℓ-zero) (ℓ-max ℓ ℓ')) where
  0b      : Poly
  1b      : Poly
  _←_     : C → D → Poly
  _∪_     : Poly → Poly → Poly  
  _·_     : Poly → Poly → Poly
  squash  : isSet Poly
  assoc   : {x y z : Poly} → (x ∪ (y ∪ z)) ≡ ((x ∪ y) ∪ z)
  rid     : {x : Poly} → x ∪ 0b ≡ x
  comm    : {x y : Poly} → x ∪ y ≡ y ∪ x
  idem    : {x : Poly} → x ∪ x ≡ x
  perm     : ∀{x1 y1 x2 y2} → x1 ← y1 · x2 ← y2 ≡ x1 ← y2 · x2 ← y1 
  assoc·   : {x y z : Poly} → x · (y · z) ≡ (x · y) · z
  rid·     : {x : Poly} → x · 1b ≡ x
  comm·    : {x y : Poly} → x · y ≡ y · x
  def∅·   : {x : Poly} → x · 0b ≡ 0b
  dist    : {x y z : Poly} → x · (y ∪ z) ≡ (x · y) ∪ (x · z)

thr· : ∀{a1 b1 a2 b2 c } → a1 · b1 ≡ a2 · b2 → a1 · c · b1 ≡ a2 · c · b2
thr· {a1} {b1} {a2} {b2} {c} eq = cong (a1 ·_) comm· ∙ assoc· ∙ cong (_· c) eq ∙ sym assoc· ∙ cong (a2 ·_) comm·

lid : ∀{x} → 0b ∪ x ≡ x
lid {x} = comm ∙ rid

lid· : ∀{x} → 1b · x ≡ x
lid· {x} = comm· ∙ rid·

ldef∅· : {x : Poly} → 0b · x ≡ 0b
ldef∅· {x} = comm· ∙ def∅·

ldist : {x y z : Poly} → (y ∪ z) · x ≡ (y · x) ∪ (z · x)
ldist {x} {y} {z} = comm· ∙ dist ∙ cong (λ a → a ∪ (x · z)) comm· ∙ cong (λ a → y · x ∪ a) comm·

∪CommMonoid : CommMonoid _
∪CommMonoid = makeCommMonoid 0b _∪_ squash (λ x y z → assoc {x} {y} {z}) (λ x → rid {x}) λ x y → comm 

PolySemillatice : Semilattice _
fst PolySemillatice = Poly
SemilatticeStr.ε (snd PolySemillatice) = 0b
SemilatticeStr._·_ (snd PolySemillatice) = _∪_
IsSemilattice.isCommMonoid (SemilatticeStr.isSemilattice (snd PolySemillatice)) = ∪CommMonoid .snd .CommMonoidStr.isCommMonoid
IsSemilattice.idem (SemilatticeStr.isSemilattice (snd PolySemillatice)) = λ x → idem


·CommMonoid : CommMonoid _
·CommMonoid = makeCommMonoid 1b _·_ squash (λ x y z → assoc·) (λ x → rid·) λ x y → comm·

PolySemiRing : SemiRing _
fst PolySemiRing = Poly 
SemiRingStr.0r (snd PolySemiRing) = 0b
SemiRingStr.1r (snd PolySemiRing) = 1b
SemiRingStr._+_ (snd PolySemiRing) = _∪_
SemiRingStr._⋆_ (snd PolySemiRing) = _·_
IsSemiRing.+IsCommMonoid (SemiRingStr.isSemiRing (snd PolySemiRing)) = ∪CommMonoid .snd .CommMonoidStr.isCommMonoid
IsSemiRing.⋆IsCommMonoid (SemiRingStr.isSemiRing (snd PolySemiRing)) = ·CommMonoid .snd .CommMonoidStr.isCommMonoid
IsSemiRing.dist (SemiRingStr.isSemiRing (snd PolySemiRing)) = λ x y z → dist



module Elim {ℓ''} {B : Poly → Type ℓ''}
       (squash* : ∀ x → isSet (B x))
       (0b* : B 0b)
       (1b* : B 1b)
       (←* : ∀ x y → B (x ← y))
       (∪* : ∀{x y} → B x → B y → B (x ∪ y))
       (·* : ∀{x y} → B x → B y → B (x · y))
       (assoc* : ∀{x y z} → (bx : B x) → (by : B y) → (bz : B z) → PathP (λ i → B (assoc {x} {y} {z} i)) (∪* bx (∪* by bz)) (∪* (∪* bx by) bz))
       (rid* : ∀{x} → (b : B x) → PathP (λ i → B (rid {x} i)) (∪* b 0b*) b)
       (comm* : ∀{x y} → (bx : B x) → (by : B y) → PathP (λ i → B (comm {x} {y} i)) (∪* bx by) (∪* by bx))
       (idem* : ∀{x} → (b : B x) → PathP (λ i → B (idem {x} i)) (∪* b b) b)
       (perm* : ∀{x1 y1 x2 y2} → PathP (λ i → B (perm {x1} {y1} {x2} {y2} i)) (·* (←* x1 y1) (←* x2 y2)) (·* (←* x1 y2) (←* x2 y1)))
       (assoc·* : ∀{x y z} → (bx : B x) → (by : B y) → (bz : B z) → PathP (λ i → B (assoc· {x} {y} {z} i)) (·* bx (·* by bz)) (·* (·* bx by) bz))
       (rid·* : ∀{x} → (b : B x) → PathP (λ i → B (rid· {x} i)) (·* b 1b*) b)
       (comm·* : ∀{x y} → (bx : B x) → (by : B y) → PathP (λ i → B (comm· {x} {y} i)) (·* bx by) (·* by bx))
       (def∅·* : ∀{x} → (bx : B x) → PathP (λ i → B (def∅· {x} i)) (·* bx 0b*) 0b*)
       (dist* : ∀{x y z} → (bx : B x) → (by : B y) → (bz : B z) → PathP (λ i → B (dist {x} {y} {z} i)) (·* bx (∪* by bz)) (∪* (·* bx by) (·* bx bz)))
       
       where

  f : (x : Poly) → B x
  f 0b = 0b*
  f 1b = 1b*
  f (x ← y) = ←* x y
  f (x ∪ y) = ∪* (f x) (f y)
  f (x · y) = ·* (f x) (f y)
  f (squash a b p1 p2 i j) = isOfHLevel→isOfHLevelDep 2 squash*  (f a) (f b) (cong f p1) (cong f p2) (squash a b p1 p2) i j
  f (assoc {x} {y} {z} i) = assoc* {x} {y} {z} (f x) (f y) (f z) i
  f (rid {x} i) = rid* (f x) i
  f (comm {x} {y} i) = comm* {x} {y} (f x) (f y) i
  f (idem {x} i) = idem* {x} (f x) i
  f (perm {x1} {y1} {x2} {y2} i) = perm* {x1} {y1} {x2} {y2} i
  f (assoc· {x} {y} {z} i) = assoc·* {x} {y} {z} (f x) (f y) (f z) i
  f (rid· {x} i) = rid·* (f x) i
  f (comm· {x} {y} i) = comm·* {x} {y} (f x) (f y) i
  f (def∅· {x} i) = def∅·* {x} (f x) i
  f (dist {x} {y} {z} i) = dist* {x} {y} {z} (f x) (f y) (f z) i

module ElimProp {ℓ''} {B : Poly → Type ℓ''}
       (BProp : ∀{x} → isProp (B x))
       (0b* : B 0b)
       (1b* : B 1b)
       (←* : ∀ x y → B (x ← y))
       (∪* : ∀{x y} → B x → B y → B (x ∪ y))
       (·* : ∀{x y} → B x → B y → B (x · y))
       where


  f : (x : Poly) → B x
  f x = Elim.f (λ x → isProp→isSet (BProp {x})) 0b* 1b* ←* ∪* ·*
               (λ {x} {y} {z} bx by bz → toPathP (BProp (transp (λ i → B (assoc {x} {y} {z} i)) i0 (∪* bx (∪* by bz))) (∪* (∪* bx by) bz)))
               (λ {x} b → toPathP (BProp (transp (λ i → B (rid {x} i)) i0 (∪* b 0b*)) b))
               (λ {x} {y} bx by → toPathP (BProp (transp (λ i → B (comm {x} {y} i)) i0 (∪* bx by)) (∪* by bx)))
               (λ {x} b → toPathP (BProp (transp (λ i → B (idem {x} i)) i0 (∪* b b)) b))
               (λ {x1} {y1} {x2} {y2} → toPathP (BProp (transp (λ i → B (perm {x1} {y1} {x2} {y2} i)) i0 (·* (←* x1 y1) (←* x2 y2))) (·* (←* x1 y2) (←* x2 y1))))
               (λ {x} {y} {z} bx by bz → toPathP (BProp (transp (λ i → B (assoc· i)) i0 (·* bx (·* by bz))) (·* (·* bx by) bz)))
               (λ {x} b → toPathP (BProp (transp (λ i → B (rid· {x} i)) i0 (·* b 1b*)) b))
               (λ {x} {y} bx by → toPathP (BProp (transp (λ i → B (comm· {x} {y} i)) i0 (·* bx by)) (·* by bx)))
               (λ {x} b → toPathP (BProp (transp (λ i → B (def∅· {x} i)) i0 (·* b 0b*)) 0b*))
               (λ {x} {y} {z} bx by bz → toPathP (BProp (transp (λ i → B (dist {x} {y} {z} i)) i0 (·* bx (∪* by bz))) (∪* (·* bx by) (·* bx bz))))
               x


module Rec {ℓ''} {B : Type ℓ''}
       (squash* : isSet B)
       (0b* : B)
       (1b* : B)
       (←*  : (x : C) → (y : D) → B)
       (∪* : B → B → B)
       (·*  : B → B → B)
       (assoc* : (bx : B) → (by : B) → (bz : B) → (∪* bx (∪* by bz)) ≡ (∪* (∪* bx by) bz))
       (rid* : (b : B) → (∪* b 0b*) ≡ b)
       (comm* : (bx : B) → (by : B) → (∪* bx by) ≡ (∪* by bx))
       (idem* : (b : B) → (∪* b b) ≡ b)
       (perm* : ∀{x1 y1 x2 y2} → (·* (←* x1 y1) (←* x2 y2)) ≡ (·* (←* x1 y2) (←* x2 y1)))
       (assoc·* : (bx : B) → (by : B) → (bz : B) → (·* bx (·* by bz)) ≡ (·* (·* bx by) bz))
       (rid·* : (b : B) → (·* b 1b*) ≡ b)
       (comm·* : (bx : B) → (by : B) → (·* bx by) ≡ (·* by bx))
       (def∅·* : (bx : B) → (·* bx 0b*) ≡ 0b*)
       (dist* : (bx : B) → (by : B) → (bz : B) → (·* bx (∪* by bz)) ≡ (∪* (·* bx by) (·* bx bz)))

       where

  f : Poly → B
  f q = Elim.f (λ _ → squash*) 0b* 1b* ←* ∪* ·* assoc* rid* comm* idem* perm* assoc·* rid·* comm·* def∅·* dist* q




