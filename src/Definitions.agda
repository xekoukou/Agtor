{-# OPTIONS  --sized-types --cubical #-}

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
  
  record ActorT (prM : UMTypePr ℓ ℓ') (UAType : Type ℓ'') : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' (ℓ-suc ℓ-zero)))) where
    open ProjStr (snd prM)
    private
      UMType = ⟨ prM ⟩
  
    field
      P       : UMType → Type
      P-isSet : (x : UMType) → isSet (P x) 
      decP  : ∀ A → Dec (P A)
      image : ∀ {A} → { p : P A } →  ⟨ ⟦ A ⟧ ⟩  → Tree UMType
      next  : ∀ {A} → { p : P A } →  ⟨ ⟦ A ⟧ ⟩  → Tree UAType
  
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

    record UATypeStr (U : Type ℓ'') : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') ℓ'')) where
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

      open MBree

      WR = WB.BSemiRing
      QR = QB.BSemiRing
  
      qisSet = IsSemiRing.is-set (SemiRingStr.isSemiRing (snd QR))
      wisSet = IsSemiRing.is-set (SemiRingStr.isSemiRing (snd WR))

      sr-hom : AC.Hom[ DWA , DQA ] → ⟨ WR ⟩ → ⟨ QR ⟩
      sr-hom ((f , g) , _) r = rec qisSet (λ x → [ l1 x ]) (λ a b r → (eq/ _ _ (Tr.elim (λ a → Tr.squash) (λ x → ∣ l2 a b x ∣) r))) r where
        l1 : WB.Bree → QB.Bree
        l1 0b = 0b
        l1 1b = 1b
        l1 (y ← x) = f y ← (g .fst x)
        l1 (ƛ_ {B} f) = ƛ (λ x → l1 (f x))
        l1 (e1 ∪ e2) = l1 e1 ∪ l1 e2
        l1 (e1 · e2) = l1 e1 · l1 e2
    
        l2 : (a b : WB.Bree) → WB.S a b → QB.S (l1 a) (l1 b)
        l2 ((x1 ← y1) · (x2 ← y2)) ((.x1 ← .y2) · (.x2 ← .y1)) perm = perm
        l2 .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = assoc _ _ _
        l2 .(b ∪ 0b) b (rid .b) = rid _
        l2 .(x ∪ y) .(y ∪ x) (comm x y) = comm _ _
        l2 .(_ ∪ c) .(_ ∪ c) (∪c c r) = ∪c _ (l2 _ _ r)
        l2 .(b ∪ b) b (idem .b) = idem _
        l2 .(x · y · z) .((x · y) · z) (assoc· x y z) = assoc· _ _ _
        l2 .(b · 1b) b (rid· .b) = rid· _
        l2 .(_ · c) .(_ · c) (·c c r) = ·c _ (l2 _ _ r)
        l2 .(x · y) .(y · x) (comm· x y) = comm· _ _
        l2 .(x · 0b) .0b (def∅· x) = def∅· _
        l2 .(x · (ƛ y)) .(ƛ (λ q → x · y q)) (defƛ· x y) = defƛ· _ _
        l2 .(x · (y ∪ z)) .(x · y ∪ x · z) (dist` x y z) = dist` _ _ _
        l2 .(ƛ (λ c → x c ∪ y c)) .((ƛ x) ∪ (ƛ y)) (distƛ∪ x y) = distƛ∪ _ _
        l2 .(ƛ (λ c → x c · y c)) .((ƛ x) · (ƛ y)) (distƛ· x y) = distƛ· _ _
        l2 .(ƛ y) .x (remƛ x y eq) = remƛ (l1 x) (λ z → l1 (y z)) λ z i → l1 (eq z i)
        l2 .(ƛ _) .(ƛ _) (ƛS f) = ƛS λ c → l2 _ _ (f c)
        l2 x y (rel-sym r) = rel-sym (l2 _ _ r)
        l2 x y (rel-trans r1 r2) = rel-trans (l2 _ _ r1) (l2 _ _ r2)
        l2 x y (rel-refl) = rel-refl

      open IsSemiRingHom
      module W = SemiRingStr (WR .snd)
      module Q = SemiRingStr (QR .snd)

      r-hom : (h : AC.Hom[ DWA , DQA ]) → IsSemiRingHom (WR .snd) (sr-hom h) (QR .snd)
      pres0 (r-hom h) = refl
      pres1 (r-hom h) = refl
      pres+ (r-hom h) = elimProp2 (λ x y → qisSet (sr-hom h (x W.+ y)) (sr-hom h x Q.+ sr-hom h y)) λ a b → refl
      pres· (r-hom h) = elimProp2 (λ x y → qisSet (sr-hom h (x W.⋆ y)) (sr-hom h x Q.⋆ sr-hom h y)) λ a b → refl
    
    
  



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
