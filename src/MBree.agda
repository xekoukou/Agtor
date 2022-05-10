{-# OPTIONS --sized-types --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Function
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma
import Cubical.Data.List as L
open import Cubical.HITs.SetQuotients as Sq
import Cubical.Relation.Binary
open import Cubical.HITs.PropositionalTruncation as Tr
open import SemiRing
open import Common



module MBree {ℓ ℓ'} {C : Type ℓ}  {D : Type ℓ'} where

infixr 5 _∪_
infixr 7 _·_
infixr 10 _←_



data Bree : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  0b      : Bree
  1b      : Bree
  _←_     : C → D → Bree
  ƛ_      : {B : Type} → (B → Bree) → Bree
  _∪_     : Bree → Bree → Bree 
  _·_     : Bree → Bree → Bree
  squash  : isSet Bree

  assoc   : {x y z : Bree} → (x ∪ (y ∪ z)) ≡ ((x ∪ y) ∪ z)
  rid     : {x : Bree} → x ∪ 0b ≡ x
  comm    : {x y : Bree} → x ∪ y ≡ y ∪ x
  idem    : {x : Bree} → x ∪ x ≡ x

  perm     : ∀{x1 y1 x2 y2} → (x1 ← y1) · (x2 ← y2) ≡ (x1 ← y2) · (x2 ← y1)
  assoc·   : {x y z : Bree} → x · (y · z) ≡ (x · y) · z
  rid·     : {x : Bree} → x · 1b ≡ x
  comm·    : {x y : Bree} → x · y ≡ y · x

  def∅·   : {x : Bree} → x · 0b ≡ 0b
  dist    : {x y z : Bree} → x · (y ∪ z) ≡ (x · y) ∪ (x · z)

  distƛ∪  : ∀{C} → {x y : C → Bree} → (ƛ λ c → (x c ∪ y c)) ≡ ((ƛ x) ∪ (ƛ y))
  distƛ·  : ∀{C} → {x y : C → Bree} → (ƛ λ c → (x c · y c)) ≡ ((ƛ x) · (ƛ y))

  remƛ    : ∀{C}→ (x : Bree) → (y : C → Bree)
            → (∀ z → y z ≡ x)
             → (ƛ y) ≡ x
  commƛ  : {B D : Type} → (f : B → D → Bree) → ƛ (λ a → ƛ λ b → f a b) ≡ ƛ λ b → ƛ λ a → f a b

lid : ∀{x} → 0b ∪ x ≡ x
lid {x} = comm ∙ rid

lid· : ∀{x} → 1b · x ≡ x
lid· {x} = comm· ∙ rid·

ldef∅· : {x : Bree} → 0b · x ≡ 0b
ldef∅· {x} = comm· ∙ def∅·

ldist : {x y z : Bree} → (y ∪ z) · x ≡ (y · x) ∪ (z · x)
ldist {x} {y} {z} = comm· ∙ dist ∙ cong (λ a → a ∪ (x · z)) comm· ∙ cong (λ a → y · x ∪ a) comm·

∪CommMonoid : CommMonoid _
∪CommMonoid = makeCommMonoid 0b _∪_ squash (λ x y z → assoc {x} {y} {z}) (λ x → rid {x}) (λ x → lid) λ x y → comm 

BreeSemillatice : Semilattice _
fst BreeSemillatice = Bree
SemilatticeStr.ε (snd BreeSemillatice) = 0b
SemilatticeStr._·_ (snd BreeSemillatice) = _∪_
IsSemilattice.isCommMonoid (SemilatticeStr.isSemilattice (snd BreeSemillatice)) = ∪CommMonoid .snd .CommMonoidStr.isCommMonoid
IsSemilattice.idem (SemilatticeStr.isSemilattice (snd BreeSemillatice)) = λ x → idem


·CommMonoid : CommMonoid _
·CommMonoid = makeCommMonoid 1b _·_ squash (λ x y z → assoc·) (λ x → rid·) (λ x → lid·) λ x y → comm·

BreeSemiRing : SemiRing _
fst BreeSemiRing = Bree
SemiRingStr.0r (snd BreeSemiRing) = 0b
SemiRingStr.1r (snd BreeSemiRing) = 1b
SemiRingStr._+_ (snd BreeSemiRing) = _∪_
SemiRingStr._⋆_ (snd BreeSemiRing) = _·_
IsSemiRing.+IsCommMonoid (SemiRingStr.isSemiRing (snd BreeSemiRing)) = ∪CommMonoid .snd .CommMonoidStr.isCommMonoid
IsSemiRing.⋆IsCommMonoid (SemiRingStr.isSemiRing (snd BreeSemiRing)) = ·CommMonoid .snd .CommMonoidStr.isCommMonoid
IsSemiRing.dist (SemiRingStr.isSemiRing (snd BreeSemiRing)) = λ x y z → dist

module Elim {ℓ''} {B : Bree → Type ℓ''}
       (squash* : ∀ x → isSet (B x))
       (0b* : B 0b)
       (1b* : B 1b)
       (←* : ∀ x y → B (x ← y))
       (ƛ* : ∀{B`} → (f : B` → Bree) → ((e : B`) → B (f e)) → B (ƛ f))
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
       (distƛ∪* : ∀{C x y fx fy} → PathP (λ i → B (distƛ∪ {C} {x} {y} i)) (ƛ* (λ c → x c ∪ y c) λ e → ∪* (fx e) (fy e)) (∪* (ƛ* x fx) (ƛ* y fy))) 
       (distƛ·* : ∀{C x y fx fy} → PathP (λ i → B (distƛ· {C} {x} {y} i)) (ƛ* (λ c → x c · y c) λ e → ·* (fx e) (fy e)) (·* (ƛ* x fx) (ƛ* y fy))) 
       (remƛ* : ∀{C x y eq fy} → (b : B x) → (eqb : ∀ z → PathP (λ i → B (eq z i)) (fy z) b) → PathP (λ i → B (remƛ {C} x y eq i)) (ƛ* y fy) b)
       (commƛ* : ∀{C D} → (f : C → D → Bree) → (fb : (a : C) → (b : D) → B (f a b)) → (PathP (λ i → B (commƛ f i)) (ƛ* (λ a → ƛ (λ b → f a b)) λ a → ƛ* (f a) (fb a) ) (ƛ* (λ b → ƛ (λ a → f a b)) λ b → ƛ* (λ a → f a b) λ a → fb a b)))
       
       where

  f : (x : Bree) → B x
  f 0b = 0b*
  f 1b = 1b*
  f (x ← y) = ←* x y
  f (ƛ x) = ƛ* x λ e → f (x e)
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
  f (distƛ∪ {C} {x} {y} i) = distƛ∪* {C} {x} {y} {λ e → f (x e)} {λ e → f ( y e)} i
  f (distƛ· {C} {x} {y} i) = distƛ·* {C} {x} {y} {λ e → f (x e)} {λ e → f ( y e)} i
  f (remƛ x y eq i) = remƛ* {_} {x} {y} {eq} {λ e → f (y e)} (f x) (λ z → cong f (eq z)) i
  f (commƛ g i) = commƛ* g (λ a b → f (g a b)) i

module ElimProp {ℓ''} {B : Bree → Type ℓ''}
       (BProp : ∀{x} → isProp (B x))
       (0b* : B 0b)
       (1b* : B 1b)
       (←* : ∀ x y → B (x ← y))
       (ƛ* : ∀{B`} → (f : B` → Bree) → ((e : B`) → B (f e)) → B (ƛ f))
       (∪* : ∀{x y} → B x → B y → B (x ∪ y))
       (·* : ∀{x y} → B x → B y → B (x · y))
       where


  f : (x : Bree) → B x
  f x = Elim.f (λ x → isProp→isSet BProp) 0b* 1b* ←* ƛ* ∪* ·*
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
               (λ {C} {x} {y} {fx} {fy} → toPathP (BProp (transp (λ i → B ((distƛ∪ {C} {x} {y} i))) i0 (ƛ* (λ c → x c ∪ y c) λ e → ∪* (fx e) (fy e))) (∪* (ƛ* x fx) (ƛ* y fy) )))
               (λ {C} {x} {y} {fx} {fy} → toPathP (BProp (transp (λ i → B ((distƛ· {C} {x} {y} i))) i0 (ƛ* (λ c → x c · y c) λ e → ·* (fx e) (fy e))) (·* (ƛ* x fx) (ƛ* y fy))))
               (λ {C} {x} {y} {eq} {fy} b eqb → toPathP (BProp (transp (λ i → B (remƛ {C} x y eq i)) i0 (ƛ* y fy)) b))
               (λ f fb → toPathP (BProp (transp (λ i → B (commƛ f i)) i0 (ƛ* (λ a → ƛ (λ b → f a b)) λ a → ƛ* (f a) (fb a))) (ƛ* (λ b → ƛ (λ a → f a b)) λ b → ƛ* (λ a → f a b) λ a → fb a b)))
               x


module Rec {ℓ''} {B : Type ℓ''}
       (squash* : isSet B)
       (0b* : B)
       (1b* : B)
       (←*  : (x : C) → (y : D) → B)
       (ƛ*  : ∀{B`} → (f : B` → Bree) → (B` → B) → B)
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
       (distƛ∪* : ∀{C x y fx fy} → (ƛ* {C} (λ c → x c ∪ y c) λ e → ∪* (fx e) (fy e)) ≡ (∪* (ƛ* x fx) (ƛ* y fy))) 
       (distƛ·* : ∀{C x y fx fy} → (ƛ* {C} (λ c → x c · y c) λ e → ·* (fx e) (fy e)) ≡ (·* (ƛ* x fx) (ƛ* y fy))) 
       (remƛ* : ∀{C} → ∀{x : Bree} → ∀{y} → {eq : (∀ z → y z ≡ x)} → ∀{fy} → (b : B) → (eqb : ∀ z → fy z ≡ b) → (ƛ* {C} y fy) ≡ b)
       (commƛ* : ∀{C D} → (f : C → D → Bree) → (fb : C → D → B) → (ƛ* (λ a → ƛ (λ b → f a b)) λ a → ƛ* (f a) (fb a) ) ≡ (ƛ* (λ b → ƛ (λ a → f a b)) λ b → ƛ* (λ a → f a b) λ a → fb a b))

       where

  f : Bree → B
  f q = Elim.f (λ _ → squash*) 0b* 1b* ←* ƛ* ∪* ·* assoc* rid* comm* idem* perm* assoc·* rid·* comm·* def∅·* dist* distƛ∪* distƛ·*
               (λ {C} {x} {y} {eq} {fy} b eqb i → remƛ* {C} {x} {y} {eq} {fy} b eqb i) commƛ* q
