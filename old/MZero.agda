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

module MZero {ℓ ℓ'} (C : Type ℓ) (D : Type ℓ') where

open MBree {_} {_} {C} {D}

module _ (cm : C → D → Bree) (decm : (x : C) → (y : D) → Dec (cm x y ≡ 0b)) where

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
  

