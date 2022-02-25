{-# OPTIONS  --confluence-check --sized-types --cubical #-}

module Definitions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Function
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_·_ ; _+_)
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets

open import Projection 
open import SemiRing
open import ProductCommMonoid
open import MTree
open import MBree

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
  
      ·WM' = TreeCommMonoid ⟨ DWM ⟩
      ·WA' = TreeCommMonoid ⟨ DWA ⟩
    
      ·QM' = TreeCommMonoid ⟨ DQM ⟩
      ·QA' = TreeCommMonoid ⟨ DQA ⟩
    
      ·WP' = ProductCommMonoid ·WM' ·WA'
      ·QP' = ProductCommMonoid ·QM' ·QA'
  
      module WB = MBree {_} {·WP'}
      module QB = MBree {_} {·QP'}

      open MBree

      WR = WB.BSemiRing
      QR = QB.BSemiRing
  
      module ·WM = CommMonoidStr (snd ·WM')
      module ·WA = CommMonoidStr (snd ·WA')
    
      module ·WP = CommMonoidStr (snd ·WP')
      module ·QP = CommMonoidStr (snd ·QP')

      qisSet = IsSemiRing.is-set (SemiRingStr.isSemiRing (snd QR))
      wisSet = IsSemiRing.is-set (SemiRingStr.isSemiRing (snd WR))

      sr-hom : AC.Hom[ DWA , DQA ] → ⟨ WR ⟩ → ⟨ QR ⟩
      sr-hom f r = rec qisSet (λ x → [ l1 x ]) (λ a b r → (eq/ _ _ (l2 a b r))) r where
        l1 : WB.Bree → QB.Bree
        l1 ∅ = ∅
        l1 (` (x , y)) = ` l14 module L1 where
         
          l11 : Tree ⟨ DWM ⟩ → Tree ⟨ DWA ⟩ → ⟨ ·QP' ⟩
          l11 x y = [ map (fst (snd (fst f))) x ] , [ map (fst (fst f)) y ]
    
          l12 : (a b : Tree ⟨ DWM ⟩) → (c : Tree ⟨ DWA ⟩) → R a b → l11 a c ≡ l11 b c
          l12 a b c r = ΣPathP ((eq/ _ _ (l121 a b r _)) , refl) where
            l121 : ∀ a b → (r : R a b) → ∀ f → R (map f a) (map f b)
            l121 .(x · (y · z)) .((x · y) · z) (assoc x y z) f = assoc _ _ _
            l121 .(b · ε) b (rid .b) f = rid _
            l121 .(x · y) .(y · x) (comm x y) f = comm _ _
            l121 .(_ · c) .(_ · c) (·c c r) f = ·c _ (l121 _ _ r f)
    
          l13 : (c : Tree ⟨ DWM ⟩) → (a b : Tree ⟨ DWA ⟩) → R a b → l11 c a ≡ l11 c b
          l13 c a b r = ΣPathP (refl , (eq/ _ _ (l131 a b r _))) where
            l131 : ∀ a b → (r : R a b) → ∀ f → R (map f a) (map f b)
            l131 .(x · (y · z)) .((x · y) · z) (assoc x y z) f = assoc _ _ _
            l131 .(b · ε) b (rid .b) f = rid _
            l131 .(x · y) .(y · x) (comm x y) f = comm _ _
            l131 .(_ · c) .(_ · c) (·c c r) f = ·c _ (l131 _ _ r f)
    
          l14 = rec2 (isSetΣ squash/ (λ _ → squash/)) l11 l12 l13 x y
        l1 (ƛ_ {B} f) = ƛ (λ x → l1 (f x))
        l1 (e1 ∪ e2) = l1 e1 ∪ l1 e2
        l1 (e1 · e2) = l1 e1 · l1 e2
    
        l2 : (a b : WB.Bree) → WB.S a b → QB.S (l1 a) (l1 b)
        l2 .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = assoc _ _ _
        l2 .(b ∪ ∅) b (rid .b) = rid _
        l2 .(x ∪ y) .(y ∪ x) (comm x y) = comm _ _
        l2 .(_ ∪ c) .(_ ∪ c) (∪c c r) = ∪c _ (l2 _ _ r)
        l2 .(b ∪ b) b (idem .b) = idem _
        l2 .(x · y · z) .((x · y) · z) (assoc· x y z) = assoc· _ _ _
        l2 .(b · ` ·WP.ε) b (rid· .b) = rid· _
        l2 .(_ · c) .(_ · c) (·c c r) = ·c _ (l2 _ _ r)
        l2 .(x · y) .(y · x) (comm· x y) = comm· _ _
        l2 .(x · ∅) .∅ (def∅· x) = def∅· _
        l2 .(` (x1 , x2) · ` (y1 , y2)) .(` (((x1 , x2)) ·WP.· (y1 , y2))) (def· (x1 , x2) (y1 , y2))
          = J (λ y eq → QB.S (` L1.l14 x1 x2 · ` L1.l14 y1 y2)
            (` y)) (def· _ _) (sym l121) where
          l121 : L1.l14 (x1 ·WM.· y1) (x2 ·WA.· y2) ≡ (L1.l14 x1 x2) ·QP.· (L1.l14 y1 y2)
          l121 = elimProp4 {P = λ x1 y1 x2 y2 → L1.l14 (x1 ·WM.· y1) (x2 ·WA.· y2) ≡ (L1.l14 x1 x2) ·QP.· (L1.l14 y1 y2)}
                   (λ x y z t → isSetΣ squash/ (λ _ → squash/) _ _) (λ a b c d → refl) x1 y1 x2 y2
        l2 .(x · (ƛ y)) .(ƛ (λ q → x · y q)) (defƛ· x y) = defƛ· _ _
        l2 .(x · (y ∪ z)) .(x · y ∪ x · z) (dist` x y z) = dist` _ _ _
        l2 .(ƛ (λ c → x c ∪ y c)) .((ƛ x) ∪ (ƛ y)) (distƛ∪ x y) = distƛ∪ _ _
        l2 .(ƛ (λ c → x c · y c)) .((ƛ x) · (ƛ y)) (distƛ· x y) = distƛ· _ _
        l2 .(ƛ y) b (remƛ .b y eq) = remƛ _ _ λ i z → l1 (eq i z)
        l2 .(ƛ _) .(ƛ _) (ƛS f) = ƛS λ c → l2 _ _ (f c)

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


