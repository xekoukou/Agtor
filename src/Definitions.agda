{-# OPTIONS --cubical #-}

module Definitions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Function
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Data.Sigma
import Cubical.Data.List as L
open import Cubical.Data.Nat hiding (_·_ ; _+_)
open import Cubical.HITs.SetQuotients
import Cubical.HITs.PropositionalTruncation as Tr
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets

open import Common
open import Projection 
open import SemiRing
open import ProductCommMonoid
open import MTree
import MBree

private
  variable
    ℓ'' : Level

UMTypePr : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
UMTypePr ℓ ℓ' = Proj ℓ (SET ℓ')

UMTypePrC : ∀ ℓ ℓ' → Category (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
UMTypePrC ℓ ℓ' = ProjC ℓ (SET ℓ')


module _ {ℓ ℓ' : _} where

  module MC = Category (UMTypePrC ℓ ℓ')
  
  record ActorT (prM : UMTypePr ℓ ℓ') (UAType : Type ℓ'') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') (ℓ-suc ℓ'')) where

    open ProjStr (snd prM)
    open MBree {ℓ = ℓ''} {ℓ' = ℓ}
    private
      UMType = ⟨ prM ⟩
  
    field
      P       : UMType → Type
      P-isSet : (x : UMType) → isSet (P x) 
      decP  : ∀ A → Dec (P A)
      next  : ∀ {A} → { p : P A } →  ⟨ ⟦ A ⟧ ⟩  → Bree {C = UAType} {D = UMType}
  
  module _ (DA DB : UMTypePr ℓ ℓ') where
  
    private
      UMA = ⟨ DA ⟩

    open ActorT
    
    record ActorHom {U1 U2 : Type ℓ''}
                    (hm : MC.Hom[ DA , DB ] )
                    (act1 : ActorT DA U1)
                    (act2 : ActorT DB U2) : Type (ℓ-max (ℓ-max ℓ' ℓ'') ℓ) where
      constructor actorhom
      field
        P→P : {A : UMA} → act1 .P A → act2 .P (fst hm A)

    open ActorHom
    
    actorHom-isSet : {U1 U2 : Type ℓ''} → ∀{hm} → {act1 : ActorT DA U1} → {act2 : ActorT DB U2}
                     → isSet (ActorHom hm act1 act2)
    actorHom-isSet {act2 = act2}
      = isSetRetract P→P actorhom (λ _ → refl) (isSetImplicitΠ λ _ → isSetΠ (λ _ → act2 .P-isSet _))

  module _ where

    record UATypeStr (U : Type ℓ'') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
      inductive
      field
        prM : UMTypePr ℓ ℓ'
        ⟦_⟧ : U → ActorT prM U
        is-set : isSet U
  
    open UATypeStr
    open ActorHom
    
    UATypePr : ∀ ℓ'' → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ''))
    UATypePr ℓ'' = TypeWithStr ℓ'' UATypeStr
  
    open Category hiding (_∘_)
  
    UATypePrC : ∀ ℓ'' → Category (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    ob (UATypePrC ℓ'') = UATypePr ℓ''
    Hom[_,_] (UATypePrC ℓ'') DA DB
      = Σ ((⟨ DA ⟩ → ⟨ DB ⟩) × MC.Hom[ prM (snd DA) , prM (snd DB) ]) λ (f , hm)
        → ∀ x → ActorHom _ _ hm (snd DA .⟦_⟧ x) (snd DB .⟦_⟧ (f x))
    id (UATypePrC ℓ'') {x} = ((λ x → x) , MC.id {prM (snd x)}) , λ y → actorhom (λ x → x)
    _⋆_ (UATypePrC ℓ'') {x} {y} {z} ((f1 , g1) , e1) ((f2 , g2) , e2)
      = (f2 ∘ f1 , (MC._⋆_ {prM (snd x)} {prM (snd y)} {prM (snd z)} g1 g2))
        , λ q → actorhom (λ r → P→P (e2 (f1 q)) (P→P (e1 q) r))
    ⋆IdL (UATypePrC ℓ'') f = refl
    ⋆IdR (UATypePrC ℓ'') f = refl
    ⋆Assoc (UATypePrC ℓ'') f g h = ΣPathP ((ΣPathP (refl , refl)) , funExt (λ x → refl))
    isSetHom (UATypePrC ℓ'') {x} {y}
      = isSetΣ (isSetΣ (isSetΠ (λ _ → (snd y) .is-set)) λ _ → MC.isSetHom {prM (snd x)} {prM (snd y)})
               λ _ → isSetΠ λ _ → actorHom-isSet _ _


  module _ {ℓ''} where
  
    module AC = Category (UATypePrC ℓ'')
  
    module _ (DWA : UATypePr ℓ'') (DQA : UATypePr ℓ'') where
  
      open UATypeStr
  
      DWM = prM (snd DWA)
      DQM = prM (snd DQA)
  
      module WB = MBree {_} {_} {⟨ DWA ⟩} {⟨ DWM ⟩}
      module QB = MBree {_} {_} {⟨ DQA ⟩} {⟨ DQM ⟩}

      sr-hom : AC.Hom[ DWA , DQA ] → WB.Bree → QB.Bree
      sr-hom hom@((f , g) , e) q
        = WB.Rec.f
           QB.squash
           QB.0b
           QB.1b
           (λ y x → f y QB.← (g .fst x))
           (λ q w → QB.ƛ w)
           (λ x y → x QB.∪ y)
           (λ x y → x QB.· y)
           (λ bx by bz i → QB.assoc {bx} {by} {bz} i)
           (λ b i → QB.rid {b} i)
           (λ bx by i → QB.comm {bx} {by} i)
           (λ b i → QB.idem {b} i)
           (λ {x1} {y1} {x2} {y2} i → QB.perm {f x1} {g .fst y1} {f x2} {g .fst y2} i)
           (λ bx by bz i → QB.assoc· {bx} {by} {bz} i)
           (λ b i → QB.rid· {b} i)
           (λ bx by i → QB.comm· {bx} {by} i)
           (λ bx i → QB.def∅· {bx} i)
           (λ bx by bz i → QB.dist {bx} {by} {bz} i)
           (λ {C} {x} {y} {fx} {fy} i → QB.distƛ∪ {C} {fx} {fy} i)
           (λ {C} {x} {y} {fx} {fy} i → QB.distƛ· {C} {fx} {fy} i)
           (λ {C} b i → QB.remƛ {C} b i)
           (λ {C} {D} f fb → QB.commƛ {C} {D} fb)
           q

      open IsSemiRingHom
      module WS = SemiRingStr (WB.BreeSemiRing .snd)
      module QS = SemiRingStr (QB.BreeSemiRing .snd)

      r-hom : (h : AC.Hom[ DWA , DQA ]) → IsSemiRingHom (WB.BreeSemiRing .snd) (sr-hom h) (QB.BreeSemiRing .snd)
      pres0 (r-hom h) = refl
      pres1 (r-hom h) = refl
      pres+ (r-hom h) x y = refl
      pres· (r-hom h) x y = refl
    
    
  



-- -- p1 : T A B → T A B
-- -- p1 (x , y) = x , [ ε ]

-- -- p2 : T A B → T A B
-- -- p2 (x , y) = [ ε ] , y

-- -- W : Type₁
-- -- W = T UType ActorT



  

-- -- m : Type₁
-- -- m = UType → UType

-- -- g : Type₁
-- -- g = ActorT → ActorT



-- -- -- --  δ    : Bree {A} → Bree
-- -- -- --  δᶜ   : Bree {A} → Bree {A} → Bree
-- -- -- -- infixr 9 δ
-- -- -- -- infixr 9 δᶜ

-- -- -- -- module _ where
-- -- -- --   open ActorT
-- -- -- --   compute : UType → ActorT → Bree {W}
-- -- -- --   compute uT actT = l1 (actT .decP uT) where
-- -- -- --     l1 : Maybe (actT .P uT) → Bree {W}
-- -- -- --     l1 (just p) = ƛ λ x → ` ([ actT .image {_} {p} x ] , [ actT .next {_} {p} x ])
-- -- -- --     l1 nothing = ∅


-- -- -- --   -- leibniz rule
-- -- -- --   lbnz    : (x y : Bree {W}) → S (δ (x · y)) 
-- -- -- --                 (((δ x) · y) ∪ (x · (δ y)) ∪ δᶜ x y)
-- -- -- --   distδ   : (x y : Bree {W}) → S (δ (x ∪ y)) (δ x ∪ δ y)
-- -- -- --   distδᶜl : (x y z : Bree {W}) → S (δᶜ (x ∪ y) z) (δᶜ x z ∪ δᶜ y z)
-- -- -- --   distδᶜr : (x y z : Bree {W}) → S (δᶜ z (x ∪ y)) (δᶜ z x ∪ δᶜ z y)
-- -- -- --   defδᶜ   : (x1 x2 : Tree UType / R) (y1 y2 : Tree ActorT / R) → S (δᶜ (` (x1 , y1)) (` (x2 , y2)) ) (δ (` (x1 , y2)) · (` (x2 , y1)) ∪ (` (x1 , y2)) · δ (` (x2 , y1)))


{-

(a1 | b1 + a2 | b2 + a3 | b3) ( c1 | z1 + c2 | z2) = a1 | z1 + a1 | z2
                                                     a2 | z1 + a2 | z2 
                                                     a3 | z1 + z3 | z2

                                                     c1 | b1 + c1 | b2 + c1 | b3
                                                     c2 | b1 + c2 | b2 + c2 | b3



-}
