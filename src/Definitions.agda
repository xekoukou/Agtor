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


open import DUniverse public 
open import SemiRing
open import ProductCommMonoid
open import MTree
open import MBree

private
  variable
    ℓ ℓ' ℓ'' : Level
 
record ActorT (DPRM : DUMType ℓ ℓ') (UAType : Type ℓ'') : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' (ℓ-suc ℓ-zero)))) where
  coinductive

  private
    open ProjStr (snd DPRM)
    UMType = ⟨ DPRM ⟩

  field
    P       : UMType → Type
    P-isSet : (x : UMType) → isSet (P x) 
    decP  : ∀ A → Dec (P A)
    image : ∀ {A} → { p : P A } →  ⟨ ⟦ A ⟧ ⟩  → Tree UMType
    next  : ∀ {A} → { p : P A } →  ⟨ ⟦ A ⟧ ⟩  → Tree UAType



module QQ (DA DB : DUMType ℓ ℓ') where

  open Category
  UMA = ⟨ DA ⟩
  UMB = ⟨ DB ⟩
  open ActorT
  module CM = Category (DUMTypeC ℓ ℓ')
  module MA = ProjStr (snd DA)
  module MB = ProjStr (snd DB)
  
  record ActorHom {U1 U2 : Type ℓ''}
                  (hm : CM.Hom[ DA , DB ] )
                  (act1 : ActorT DA U1)
                  (act2 : ActorT DB U2) : Type (ℓ-max (ℓ-max ℓ' ℓ'') ℓ) where
    constructor actorhom
    field
      CP : {A : UMA} → act1 .P A → act2 .P (fst hm A)

  actorHom-isSet : {U1 U2 : Type ℓ''} → ∀{hm} → {act1 : ActorT DA U1} → {act2 : ActorT DB U2}
                   → isSet (ActorHom hm act1 act2)
  actorHom-isSet {act2 = act2}
    = isSetRetract ActorHom.CP actorhom (λ _ → refl) (isSetImplicitΠ λ _ → isSetΠ (λ _ → act2 .P-isSet _))

module EE (ℓ ℓ' : _) where

  open Category hiding (_∘_)
  module CM = Category (DUMTypeC ℓ ℓ')

  record DUATypeStr (U : Type ℓ'') : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') ℓ'')) where
    inductive
    field
      D : DUMType ℓ ℓ'
      ⟦_⟧ : U → ActorT D U
      is-set : isSet U

  open DUATypeStr
  
  DUAType : ∀ ℓ'' → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ''))
  DUAType ℓ'' = TypeWithStr ℓ'' DUATypeStr

  DUATypeC : ∀ ℓ'' → Category (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  ob (DUATypeC ℓ'') = DUAType ℓ''
  Hom[_,_] (DUATypeC ℓ'') DA DB
    = Σ ((⟨ DA ⟩ → ⟨ DB ⟩) × CM.Hom[ D (snd DA) , D (snd DB) ]) λ (f , hm)
      → ∀ x → QQ.ActorHom _ _ hm (snd DA .⟦_⟧ x) (snd DB .⟦_⟧ (f x))
  id (DUATypeC ℓ'') {x} = ((λ x → x) , CM.id {D (snd x)}) , λ y → QQ.actorhom (λ x → x)
  _⋆_ (DUATypeC ℓ'') {x} {y} {z} ((f1 , g1) , e1) ((f2 , g2) , e2)
    = (f2 ∘ f1 , (CM._⋆_ {D (snd x)} {D (snd y)} {D (snd z)} g1 g2))
      , λ q → QQ.actorhom (λ r → QQ.ActorHom.CP (e2 (f1 q)) (QQ.ActorHom.CP (e1 q) r))
  ⋆IdL (DUATypeC ℓ'') f = refl
  ⋆IdR (DUATypeC ℓ'') f = refl
  ⋆Assoc (DUATypeC ℓ'') f g h = ΣPathP ((ΣPathP (refl , refl)) , funExt (λ x → refl))
  isSetHom (DUATypeC ℓ'') {x} {y}
    = isSetΣ (isSetΣ (isSetΠ (λ _ → (snd y) .is-set)) λ _ → CM.isSetHom {D (snd x)} {D (snd y)})
             λ _ → isSetΠ λ _ → QQ.actorHom-isSet _ _
  


open EE

module _ (DWA : DUAType ℓ ℓ' ℓ'') (DQA : DUAType ℓ ℓ' ℓ'') where

  module AC = Category (DUATypeC ℓ ℓ' ℓ'')
  module MC = Category (DUMTypeC ℓ ℓ')

  open DUATypeStr

  DWM = D (snd DWA)
  DQM = D (snd DQA)

  ·WM' = TreeCommMonoid ⟨ DWM ⟩
  ·WA' = TreeCommMonoid ⟨ DWA ⟩

  ·QM' = TreeCommMonoid ⟨ DQM ⟩
  ·QA' = TreeCommMonoid ⟨ DQA ⟩

  module ·WM = CommMonoidStr (snd ·WM')
  module ·WA = CommMonoidStr (snd ·WA')

  ·WP' = ProductCommMonoid ·WM' ·WA'
  ·QP' = ProductCommMonoid ·QM' ·QA'


  module ·WP = CommMonoidStr (snd ·WP')
  module ·QP = CommMonoidStr (snd ·QP')

  module WMB = MBree ·WP'
  module QMB = MBree ·QP'

  WR = WMB.BSemiRing
  QR = QMB.BSemiRing

  module WSR = SemiRingStr (snd WR)
  module QSR = SemiRingStr (snd QR)

  module WSRI = IsSemiRing WSR.isSemiRing
  module QSRI = IsSemiRing QSR.isSemiRing


  open MBree
  
  rr : AC.Hom[ DWA , DQA ] → ⟨ WR ⟩ → ⟨ QR ⟩
  rr f r = rec QSRI.is-set (λ x → [ l1 x ]) (λ a b r → (eq/ _ _ (l12 a b r))) r where
    l1 : WMB.Bree → QMB.Bree
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

    l12 : (a b : WMB.Bree) → WMB.S a b → QMB.S (l1 a) (l1 b)
    l12 .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = assoc _ _ _
    l12 .(b ∪ ∅) b (rid .b) = rid _
    l12 .(x ∪ y) .(y ∪ x) (comm x y) = comm _ _
    l12 .(_ ∪ c) .(_ ∪ c) (∪c c r) = ∪c _ (l12 _ _ r)
    l12 .(b ∪ b) b (idem .b) = idem _
    l12 .(x · y · z) .((x · y) · z) (assoc· x y z) = assoc· _ _ _
    l12 .(b · ` ·WP.ε) b (rid· .b) = rid· _
    l12 .(_ · c) .(_ · c) (·c c r) = ·c _ (l12 _ _ r)
    l12 .(x · y) .(y · x) (comm· x y) = comm· _ _
    l12 .(x · ∅) .∅ (def∅· x) = def∅· _
    l12 .(` (x1 , x2) · ` (y1 , y2)) .(` (((x1 , x2)) ·WP.· (y1 , y2))) (def· (x1 , x2) (y1 , y2)) = J (λ y eq → QMB.S (QMB.` L1.l14 x1 x2 QMB.· QMB.` L1.l14 y1 y2)
     (QMB.` y)) (def· _ _) (sym l121) where
      l121 : L1.l14 (x1 ·WM.· y1) (x2 ·WA.· y2) ≡ (L1.l14 x1 x2) ·QP.· (L1.l14 y1 y2)
      l121 = elimProp4 {P = λ x1 y1 x2 y2 → L1.l14 (x1 ·WM.· y1) (x2 ·WA.· y2) ≡ (L1.l14 x1 x2) ·QP.· (L1.l14 y1 y2)}
               (λ x y z t → isSetΣ squash/ (λ _ → squash/) _ _) (λ a b c d → refl) x1 y1 x2 y2
    l12 .(x · (ƛ y)) .(ƛ (λ q → x · y q)) (defƛ· x y) = defƛ· _ _
    l12 .(x · (y ∪ z)) .(x · y ∪ x · z) (dist` x y z) = dist` _ _ _
    l12 .(ƛ (λ c → x c ∪ y c)) .((ƛ x) ∪ (ƛ y)) (distƛ∪ x y) = distƛ∪ _ _
    l12 .(ƛ (λ c → x c · y c)) .((ƛ x) · (ƛ y)) (distƛ· x y) = distƛ· _ _
    l12 .(ƛ y) b (remƛ .b y eq) = remƛ _ _ λ i z → l1 (eq i z)
    l12 .(ƛ _) .(ƛ _) (ƛS f) = ƛS λ c → l12 _ _ (f c)














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


