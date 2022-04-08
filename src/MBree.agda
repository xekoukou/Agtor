{-# OPTIONS  --confluence-check --sized-types --cubical #-}

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

data Bree : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  0b   : Bree
  1b   : Bree
  _←_  : C → D → Bree
  ƛ_   : {B : Type} → (B → Bree) → Bree
  _∪_  : Bree → Bree → Bree 
  _·_  : Bree → Bree → Bree

infixr 5 _∪_
infixr 7 _·_
infixr 10 _←_


data S : Bree → Bree → Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  assoc   : (x y z : Bree) → S (x ∪ (y ∪ z)) ((x ∪ y) ∪ z)
  rid     : (x : Bree) → S (x ∪ 0b) x
  comm    : (x y : Bree) → S (x ∪ y) (y ∪ x)
  ∪c      : {x y : Bree} → (c : Bree) → S x y → S (x ∪ c) (y ∪ c)
  
  idem    : (x : Bree) → S (x ∪ x) x

  perm    : ∀{x1 y1 x2 y2} → S ((x1 ← y1) · (x2 ← y2)) ((x1 ← y2) · (x2 ← y1))
  assoc·   : (x y z : Bree) → S (x · (y · z)) ((x · y) · z)
  rid·     : (x : Bree) → S (x · 1b) x
  ·c      : {x y : Bree} → (c : Bree) → S x y → S (x · c) (y · c)
  comm·   : (x y : Bree) → S (x · y) (y · x)

  def∅·   : (x : Bree) → S (x · 0b) 0b
  defƛ·   : ∀{C} → (x : Bree) → (y : C → Bree) → S (x · (ƛ y)) (ƛ λ q → x · (y q))
  dist`   : (x y z : Bree) → S (x · (y ∪ z)) ((x · y) ∪ (x · z))

  distƛ∪  : ∀{C} → (x y : C → Bree) → S (ƛ λ c → (x c ∪ y c)) (ƛ x ∪ ƛ y)
  distƛ·  : ∀{C} → (x y : C → Bree) → S (ƛ λ c → (x c · y c)) (ƛ x · ƛ y)
  -- More involved equaility on lambdas.
  -- Maybe instead of doing this, we introduce an equality that considers cases between open terms and closed terms.
  remƛ    : ∀{C}→ (x : Bree) → (y : C → Bree)
            → (∀ z → y z ≡ x)
            → S (ƛ y) x
  ƛS      : ∀{C} → {x y : C → Bree} → ((c : C) → S (x c) (y c)) → S (ƛ x) (ƛ y)
  rel-refl   : ∀{x} → S x x
  rel-sym   : ∀{x y} → S x y → S y x
  rel-trans : ∀{x y z} → S x y → S y z → S x z




module _ where

  open Cubical.Relation.Binary
  open BinaryRelation

  ∥S∥ : ∀ a b → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
  ∥S∥ a b = Tr.∥ S a b ∥

  ∥S∥isPropValued : isPropValued ∥S∥
  ∥S∥isPropValued a b x y = Tr.squash x y

  SisEquivRel : isEquivRel S
  isEquivRel.reflexive SisEquivRel a = rel-refl
  isEquivRel.symmetric SisEquivRel a b r = rel-sym r
  isEquivRel.transitive SisEquivRel a b c r z = rel-trans r z

  ∥S∥isEquivRel : isEquivRel ∥S∥
  isEquivRel.reflexive ∥S∥isEquivRel a = Tr.∣ rel-refl ∣
  isEquivRel.symmetric ∥S∥isEquivRel a b r = Tr.elim (λ x → Tr.squash) (λ x →  Tr.∣ rel-sym x ∣) r
  isEquivRel.transitive ∥S∥isEquivRel a b c r z = Tr.elim2 (λ x y → Tr.squash) (λ a b → Tr.∣ rel-trans a b ∣) r z

  IsoEqS : ∀ (a b : Bree) → Iso ([ a ] ≡ [ b ]) (∥S∥ a b)
  IsoEqS a b = isEquivRel→effectiveIso ∥S∥isPropValued ∥S∥isEquivRel a b


∪c≡' : {a b : Bree} → (c : Bree) → S a b → Path (Bree / ∥S∥) [ a ∪ c ] [ b ∪ c ]
∪c≡' c r = eq/ _ _ (∣ ∪c c r ∣)


∪c≡ : {a b : Bree} → (c : Bree) → ∥S∥ a b → Path (Bree / ∥S∥) [ a ∪ c ] [ b ∪ c ]
∪c≡ c r = Tr.elim (λ _ → squash/ _ _) (∪c≡' c) r

c∪≡ : {a b : Bree} → (c : Bree) → ∥S∥ a b → [ c ∪ a ] ≡ [ c ∪ b ]
c∪≡ c r = eq/ _ _ (∣ comm _ _ ∣) ∙∙ ∪c≡ c r ∙∙ eq/ _ _ (∣ comm _ _ ∣)

∪≡ : {a1 a2 b1 b2 : Bree} → ∥S∥ a1 a2 → ∥S∥ b1 b2 → Path (Bree / ∥S∥) [ a1 ∪ b1 ] [ a2 ∪ b2 ]
∪≡ r1 r2 = ∪c≡ _ r1 ∙ c∪≡ _ r2 

private
  _⋃_ : Bree / ∥S∥ → Bree / ∥S∥ → Bree / ∥S∥
  _⋃_ a b = Sq.rec2 squash/ (λ a b → [ a ∪ b ]) (λ _ _ → ∪c≡) (λ c _ _ → c∪≡ c) a b
  
  
  
  assoc⋃ : (x y z : Bree / ∥S∥) → (x ⋃ (y ⋃ z)) ≡ ((x ⋃ y) ⋃ z)
  assoc⋃ = elimProp3 (λ x y z → squash/ ((x ⋃ (y ⋃ z))) (((x ⋃ y) ⋃ z)))
                     (λ x y z → eq/ _ _ (∣ assoc x y z ∣))
  
  rid⋃ : (x : Bree / ∥S∥) → (x ⋃ [ 0b ]) ≡ x
  rid⋃ = elimProp (λ x → squash/ (x ⋃ [ 0b ]) x)
                  (λ x → eq/ _ _ (∣ rid x ∣))
  
  comm⋃ : (x y : Bree / ∥S∥) → (x ⋃ y) ≡ (y ⋃ x)
  comm⋃ = elimProp2 (λ x y → squash/ _ _)
                  (λ x y → eq/ _ _ (∣ comm x y ∣))
  
  
  idem⋃ : (x : Bree / ∥S∥) → (x ⋃ x) ≡ x
  idem⋃ = elimProp (λ x → squash/ (x ⋃ x) x) λ a → eq/ _ _ (∣ idem a ∣)
  
    
BCommMonoid : CommMonoid _
BCommMonoid = makeCommMonoid [ 0b ] _⋃_ squash/ assoc⋃ rid⋃ (λ x → comm⋃ _ x ∙ rid⋃ x)  comm⋃

BSemillatice : Semilattice _
fst BSemillatice = Bree / ∥S∥
SemilatticeStr.ε (snd BSemillatice) = [ 0b ]
SemilatticeStr._·_ (snd BSemillatice) = _⋃_
IsSemilattice.isCommMonoid (SemilatticeStr.isSemilattice (snd BSemillatice))
  = BCommMonoid .snd .CommMonoidStr.isCommMonoid
IsSemilattice.idem (SemilatticeStr.isSemilattice (snd BSemillatice)) = idem⋃


·c≡ : {a b : Bree} → (c : Bree) → ∥S∥ a b → Path (Bree / ∥S∥) [ a · c ] [ b · c ]
·c≡ c r = Tr.elim (λ a → squash/ _ _) (λ x → eq/ _ _ (∣ ·c c x ∣) ) r

c·≡ : {a b : Bree} → (c : Bree) → ∥S∥ a b → [ c · a ] ≡ [ c · b ]
c·≡ c r = eq/ _ _ (∣ comm· _ _ ∣) ∙∙ ·c≡ c r ∙∙ eq/ _ _ (∣ comm· _ _ ∣)

·≡ : {a1 a2 b1 b2 : Bree} → ∥S∥ a1 a2 → ∥S∥ b1 b2 → Path (Bree / ∥S∥) [ a1 · b1 ] [ a2 · b2 ]
·≡ r1 r2 = ·c≡ _ r1 ∙ c·≡ _ r2 

private
  _··_ : Bree / ∥S∥ → Bree / ∥S∥ → Bree / ∥S∥
  _··_ a b = Sq.rec2 squash/ (λ a b → [ a · b ]) (λ _ _ → ·c≡) (λ c _ _ → c·≡ c) a b
  
  ι : Bree / ∥S∥
  ι = [ 1b ]
  
  assoc·· : (x y z : Bree / ∥S∥) → (x ·· (y ·· z)) ≡ ((x ·· y) ·· z)
  assoc·· = elimProp3 (λ x y z → squash/ ((x ·· (y ·· z))) (((x ·· y) ·· z)))
                     (λ x y z → eq/ _ _ (∣ assoc· x y z ∣))
  
  rid·· : (x : Bree / ∥S∥) → (x ··  ι) ≡ x
  rid·· = elimProp (λ x → squash/ (x ··  ι ) x)
                  (λ x → eq/ _ _ (∣ rid· x ∣))
  
  comm·· : (x y : Bree / ∥S∥) → (x ·· y) ≡ (y ·· x)
  comm·· = elimProp2 (λ x y → squash/ _ _)
                  (λ x y → eq/ _ _ (∣ comm· x y ∣))
  
  
  dist·· : (a b c : Bree / ∥S∥) → (a ·· (b ⋃ c)) ≡ (a ·· b) ⋃ (a ·· c)
  dist·· = elimProp3 (λ x y z → squash/ (x ·· (y ⋃ z)) ((x ·· y) ⋃ (x ·· z)))
                     λ a b c → eq/ _ _ (∣ dist` _ _ _ ∣) 
  
B·CommMonoid : CommMonoid _
B·CommMonoid = makeCommMonoid ι _··_ squash/ assoc·· rid·· (λ x → comm·· _ x ∙ rid·· x)  comm··

BSemiRing : SemiRing _
fst BSemiRing = Bree / ∥S∥
SemiRingStr.0r (snd BSemiRing) = [ 0b ]
SemiRingStr.1r (snd BSemiRing) =  ι
SemiRingStr._+_ (snd BSemiRing) = _⋃_
SemiRingStr._⋆_ (snd BSemiRing) = _··_
IsSemiRing.+IsCommMonoid (SemiRingStr.isSemiRing (snd BSemiRing))
  = (snd BCommMonoid) .CommMonoidStr.isCommMonoid
IsSemiRing.⋆IsCommMonoid (SemiRingStr.isSemiRing (snd BSemiRing))
  = (snd B·CommMonoid) .CommMonoidStr.isCommMonoid
IsSemiRing.dist (SemiRingStr.isSemiRing (snd BSemiRing)) = dist··

