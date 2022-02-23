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
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Maybe hiding (rec)
open import Cubical.Codata.Stream
open import Cubical.Data.Nat hiding (_·_ ; _+_)
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Categories.Category

module Br = BinaryRelation

open import DUniverse public 

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ




record IsSemiRing {R : Type ℓ}
              (0r 1r : R) (_+_ _⋆_ : R → R → R) : Type ℓ  where

  constructor issemiring

  field
    +IsCommMonoid  : IsCommMonoid 0r _+_
    ⋆IsCommMonoid  : IsCommMonoid 1r _⋆_
    dist           : (x y z : R) → (x ⋆ (y + z) ≡ (x ⋆ y) + (x ⋆ z))

  open IsCommMonoid ⋆IsCommMonoid public
    renaming
      ( assoc       to ⋆Assoc
      ; identity    to ⋆Identity
      ; lid         to ⋆Lid
      ; rid         to ⋆Rid
      ; isSemigroup to ⋆IsSemigroup
      ; comm        to ⋆comm )

  open IsCommMonoid +IsCommMonoid public
    renaming
      ( assoc       to +Assoc
      ; identity    to +Identity
      ; lid         to +Lid
      ; rid         to +Rid
      ; isSemigroup to +IsSemigroup
      ; comm        to +comm )
    hiding
      ( is-set ) -- We only want to export one proof of this

record SemiRingStr (R : Type ℓ) : Type ℓ  where
  field
    0r  : R
    1r  : R
    _+_ : R → R → R
    _⋆_ : R → R → R
    isSemiRing : IsSemiRing 0r 1r _+_ _⋆_


SemiRing : ∀ ℓ → Type (ℓ-suc ℓ) 
SemiRing _ = TypeWithStr _ SemiRingStr




record IsSemiRingHom {A : Type ℓ} {B : Type ℓ'} (Q : SemiRingStr A) (f : A → B) (W : SemiRingStr B)
  : Type (ℓ-max ℓ ℓ')
  where

  -- Shorter qualified names
  private
    module Q = SemiRingStr Q
    module W = SemiRingStr W

  field
    pres0 : f Q.0r ≡ W.0r
    pres1 : f Q.1r ≡ W.1r
    pres+ : (x y : A) → f (x Q.+ y) ≡ f x W.+ f y
    pres· : (x y : A) → f (x Q.⋆ y) ≡ f x W.⋆ f y

SemiRingHom : (L : SemiRing ℓ) (M : SemiRing ℓ') → Type _
SemiRingHom L M = Σ[ f ∈ (⟨ L ⟩ → ⟨ M ⟩) ] IsSemiRingHom (L .snd) f (M .snd)




data Tree (A : Type ℓ) : Type ℓ where
  ε    : Tree A
  `_   : A → Tree A
  _·_  : Tree A → Tree A → Tree A


thom : ∀{A B : Type ℓ} → (f : A → B) → Tree A → Tree B
thom f ε = ε
thom f (` x) = ` (f x)
thom f (t1 · t2) = thom f t1 · thom f t2

thom-id : ∀{A : Type ℓ} → (x : Tree A) → thom (λ y → y) x ≡ x
thom-id ε = refl
thom-id (` x) = refl
thom-id (x · y) with thom-id x | thom-id y
... | r | w = cong₂ (λ a b → a · b) r w

data R {A : Type ℓ} : Tree A → Tree A → Type ℓ where
  assoc  : (x y z : Tree A) → R (x · (y · z)) ((x · y) · z)
  rid    : (x : Tree A) → R (x · ε) x
  comm   :  (x y : Tree A) → R (x · y) (y · x)
  ·c     : {x y : Tree A} →  (c : Tree A) → R x y → R (x · c) (y · c)


_*_ : Tree A / R → Tree A / R →  Tree A / R
_*_ {A = A} a b = rec2 squash/ (λ a b → [ a · b ]) l1 l2 a b where
  l1 : (a b c : Tree A) → R a b → [ a · c ] ≡ [ b · c ]
  l1 a b c r = eq/ _ _ (·c c r)
  
  l2 : (c a b : Tree A) → R a b → [ c · a ] ≡ [ c · b ]
  l2 c a b r = eq/ _ _ (comm _ _) ∙∙ l1 a b c r ∙∙ eq/ _ _ (comm _ _)



assoc* : (x y z : Tree A / R) → (x * (y * z)) ≡ ((x * y) * z)
assoc* = elimProp3 (λ x y z → squash/ ((x * (y * z))) (((x * y) * z)))
                   (λ x y z → eq/ _ _ (assoc x y z))

rid* : (x : Tree A / R) → (x * [ ε ]) ≡ x
rid* = elimProp (λ x → squash/ (x * [ ε ]) x)
                (λ x → eq/ _ _ (rid x))

comm* : (x y : Tree A / R) → (x * y) ≡ (y * x)
comm* = elimProp2 (λ x y → squash/ _ _)
                (λ x y → eq/ _ _ (comm x y))

TreeCommMonoid : {A : Type ℓ} → CommMonoid _
TreeCommMonoid {_} {A} = makeCommMonoid [ ε {_} {A} ] _*_ squash/ assoc* rid* (λ x → comm* _ x ∙ rid* x) comm*

T : (A : Type ℓ) → (B : Type ℓ') → _
T A B = Tree A / R × Tree B / R


_**_ : T A B → T A B → T A B
_**_ (x1 , y1) (x2 , y2) = x1 * x2 , y1 * y2

dd : isSet A → isSet B → isSet (A × B)
dd isa isb (x1 , y1) (x2 , y2) p1 p2
  = let xp1 , yp1 = PathPΣ p1
        xp2 , yp2 = PathPΣ p2
    in cong ΣPathP (λ i → isa _ _ xp1 xp2 i , isb _ _ yp1 yp2 i)

ddp : (x y : T A B) → isProp (x ≡ y)
ddp = dd squash/ squash/

assoc** : (x y z : Σ (Tree A / R) (λ _ → Tree B / R)) →
          (x ** (y ** z)) ≡ ((x ** y) ** z)
assoc** (x1 , x2) (y1 , y2) (z1 , z2) = λ i → (assoc* x1 y1 z1 i) , (assoc* x2 y2 z2 i)

rid** : (x : Σ (Tree A / R) (λ _ → Tree B / R)) →
         (x ** ([ ε ] , [ ε ])) ≡ x
rid** (x1 , x2) i = (rid* x1 i) , (rid* x2 i)

lid** : (x : Σ (Tree A / R) (λ _ → Tree B / R)) →
         (([ ε ] , [ ε ]) ** x) ≡ x
lid** (x1 , x2) i = ((comm* _ x1 ∙ rid* x1) i) , (((comm* _ x2 ∙ rid* x2) i))

comm** : (x y : Σ (Tree A / R) (λ _ → Tree B / R)) →
          (x ** y) ≡ (y ** x)
comm** (x1 , x2) (y1 , y2) = λ i → (comm* x1 y1 i) , (comm* x2 y2 i)


TCommMonoid : {A : Type ℓ} {B : Type ℓ'} → CommMonoid _
TCommMonoid {_} {_} {A} {B} = makeCommMonoid ([ ε {_} {A} ] , [ ε {_} {B} ]) _**_
                                    (dd squash/ squash/) assoc** rid** lid** comm**

module MBree (·monoid : CommMonoid ℓ) where

  C = ⟨ ·monoid ⟩
  module Q = CommMonoidStr (snd ·monoid)
  module E = IsCommMonoid Q.isCommMonoid
  
  data Bree : Type (ℓ-suc ℓ) where
    ∅    : Bree
    `_   : C → Bree
    ƛ_    : {B : Type} → (B → Bree) → Bree
    _∪_  : Bree → Bree → Bree 
    _·_  : Bree → Bree → Bree
  
  infixr 5 _∪_
  infixr 7 _·_
  infixr 10 `_
  
  data S : Bree → Bree → Type (ℓ-suc ℓ) where
    assoc   : (x y z : Bree) → S (x ∪ (y ∪ z)) ((x ∪ y) ∪ z)
    rid     : (x : Bree) → S (x ∪ ∅) x
    comm    : (x y : Bree) → S (x ∪ y) (y ∪ x)
    ∪c      : {x y : Bree} → (c : Bree) → S x y → S (x ∪ c) (y ∪ c)
    
    idem    : (x : Bree) → S (x ∪ x) x
  
    assoc·   : (x y z : Bree) → S (x · (y · z)) ((x · y) · z)
    rid·     : (x : Bree) → S (x · ` Q.ε) x
    ·c      : {x y : Bree} → (c : Bree) → S x y → S (x · c) (y · c)
    comm·   : (x y : Bree) → S (x · y) (y · x)
  
    def∅·   : (x : Bree) → S (x · ∅) ∅
    def·    : (x y : C) → S ((` x) · (` y)) (` (x Q.· y))
    defƛ·   : ∀{C} → (x : Bree) → (y : C → Bree) → S (x · (ƛ y)) (ƛ λ q → x · (y q))
    dist`   : (x y z : Bree) → S (x · (y ∪ z)) ((x · y) ∪ (x · z))
  
    distƛ∪  : ∀{C} → (x y : C → Bree) → S (ƛ λ c → (x c ∪ y c)) (ƛ x ∪ ƛ y)
    distƛ·  : ∀{C} → (x y : C → Bree) → S (ƛ λ c → (x c · y c)) (ƛ x · ƛ y)
    remƛ    : ∀{C} → (x : Bree) → (y : C → Bree) → y ≡ (λ _ → x) → S (ƛ y) x
    ƛS      : ∀{C} → {x y : C → Bree} → ((c : C) → S (x c) (y c)) → S (ƛ x) (ƛ y)
  
--  r-sym  : {x y : Bree {W}} → S x y → S y x
--  r-refl : {x : Bree {W}} → S x x
--  r-trans : {x y z : Bree {W}} → S x y → S y z → S x z

  
  ∪c≡ : {a b : Bree} → (c : Bree) → S a b → Path (Bree / S) [ a ∪ c ] [ b ∪ c ]
  ∪c≡ c r = eq/ _ _ (∪c c r)
  
  c∪≡ : {a b : Bree} → (c : Bree) → S a b → [ c ∪ a ] ≡ [ c ∪ b ]
  c∪≡ c r = eq/ _ _ (comm _ _) ∙∙ ∪c≡ c r ∙∙ eq/ _ _ (comm _ _)
  
  ∪≡ : {a1 a2 b1 b2 : Bree} → S a1 a2 → S b1 b2 → Path (Bree / S) [ a1 ∪ b1 ] [ a2 ∪ b2 ]
  ∪≡ r1 r2 = ∪c≡ _ r1 ∙ c∪≡ _ r2 
  
  
  _⋃_ : Bree / S → Bree / S → Bree / S
  _⋃_ a b = rec2 squash/ (λ a b → [ a ∪ b ]) (λ _ _ → ∪c≡) (λ c _ _ → c∪≡ c) a b
  
  
  
  assoc⋃ : (x y z : Bree / S) → (x ⋃ (y ⋃ z)) ≡ ((x ⋃ y) ⋃ z)
  assoc⋃ = elimProp3 (λ x y z → squash/ ((x ⋃ (y ⋃ z))) (((x ⋃ y) ⋃ z)))
                     (λ x y z → eq/ _ _ (assoc x y z))
  
  rid⋃ : (x : Bree / S) → (x ⋃ [ ∅ ]) ≡ x
  rid⋃ = elimProp (λ x → squash/ (x ⋃ [ ∅ ]) x)
                  (λ x → eq/ _ _ (rid x))
  
  comm⋃ : (x y : Bree / S) → (x ⋃ y) ≡ (y ⋃ x)
  comm⋃ = elimProp2 (λ x y → squash/ _ _)
                  (λ x y → eq/ _ _ (comm x y))
  
  
  idem⋃ : (x : Bree / S) → (x ⋃ x) ≡ x
  idem⋃ = elimProp (λ x → squash/ (x ⋃ x) x) λ a → eq/ _ _ (idem a)
  
    
  BCommMonoid : CommMonoid _
  BCommMonoid = makeCommMonoid [ ∅ ] _⋃_ squash/ assoc⋃ rid⋃ (λ x → comm⋃ _ x ∙ rid⋃ x)  comm⋃
  
  BSemillatice : Semilattice _
  fst BSemillatice = Bree / S
  SemilatticeStr.ε (snd BSemillatice) = [ ∅ ]
  SemilatticeStr._·_ (snd BSemillatice) = _⋃_
  IsSemilattice.isCommMonoid (SemilatticeStr.isSemilattice (snd BSemillatice)) = BCommMonoid .snd .CommMonoidStr.isCommMonoid
  IsSemilattice.idem (SemilatticeStr.isSemilattice (snd BSemillatice)) = idem⋃
  
  
  ·c≡ : {a b : Bree} → (c : Bree) → S a b → Path (Bree / S) [ a · c ] [ b · c ]
  ·c≡ c r = eq/ _ _ (·c c r)
  
  c·≡ : {a b : Bree} → (c : Bree) → S a b → [ c · a ] ≡ [ c · b ]
  c·≡ c r = eq/ _ _ (comm· _ _) ∙∙ ·c≡ c r ∙∙ eq/ _ _ (comm· _ _)
  
  ·≡ : {a1 a2 b1 b2 : Bree} → S a1 a2 → S b1 b2 → Path (Bree / S) [ a1 · b1 ] [ a2 · b2 ]
  ·≡ r1 r2 = ·c≡ _ r1 ∙ c·≡ _ r2 
  
  _··_ : Bree / S → Bree / S → Bree / S
  _··_ a b = rec2 squash/ (λ a b → [ a · b ]) (λ _ _ → ·c≡) (λ c _ _ → c·≡ c) a b
  
  ι : Bree / S
  ι = [ ` Q.ε ]
  
  assoc·· : (x y z : Bree / S) → (x ·· (y ·· z)) ≡ ((x ·· y) ·· z)
  assoc·· = elimProp3 (λ x y z → squash/ ((x ·· (y ·· z))) (((x ·· y) ·· z)))
                     (λ x y z → eq/ _ _ (assoc· x y z))
  
  rid·· : (x : Bree / S) → (x ··  ι) ≡ x
  rid·· = elimProp (λ x → squash/ (x ··  ι ) x)
                  (λ x → eq/ _ _ (rid· x))
  
  comm·· : (x y : Bree / S) → (x ·· y) ≡ (y ·· x)
  comm·· = elimProp2 (λ x y → squash/ _ _)
                  (λ x y → eq/ _ _ (comm· x y))
  
  
  dist·· : (a b c : Bree / S) → (a ·· (b ⋃ c)) ≡ (a ·· b) ⋃ (a ·· c)
  dist·· = elimProp3 (λ x y z → squash/ (x ·· (y ⋃ z)) ((x ·· y) ⋃ (x ·· z)))
                     λ a b c → eq/ _ _ (dist` _ _ _) 
  
  B·CommMonoid : CommMonoid _
  B·CommMonoid = makeCommMonoid ι _··_ squash/ assoc·· rid·· (λ x → comm·· _ x ∙ rid·· x)  comm··

  BSemiRing : SemiRing _
  fst BSemiRing = Bree / S
  SemiRingStr.0r (snd BSemiRing) = [ ∅ ]
  SemiRingStr.1r (snd BSemiRing) =  ι
  SemiRingStr._+_ (snd BSemiRing) = _⋃_
  SemiRingStr._⋆_ (snd BSemiRing) = _··_
  IsSemiRing.+IsCommMonoid (SemiRingStr.isSemiRing (snd BSemiRing)) = (snd BCommMonoid) .CommMonoidStr.isCommMonoid
  IsSemiRing.⋆IsCommMonoid (SemiRingStr.isSemiRing (snd BSemiRing)) = (snd B·CommMonoid) .CommMonoidStr.isCommMonoid
  IsSemiRing.dist (SemiRingStr.isSemiRing (snd BSemiRing)) = dist··
  
  
  
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


  ·WCom = TCommMonoid {_} {_} {⟨ DWM ⟩} {⟨ DWA ⟩}
  ·QCom = TCommMonoid {_} {_} {⟨ DQM ⟩} {⟨ DQA ⟩}

  module WMB = MBree ·WCom
  module QMB = MBree ·QCom

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
     
      l11 : Tree ⟨ DWM ⟩ → Tree ⟨ DWA ⟩ → QMB.C
      l11 x y = [ thom (fst (snd (fst f))) x ] , [ thom (fst (fst f)) y ]

      l12 : (a b : Tree ⟨ DWM ⟩) → (c : Tree ⟨ DWA ⟩) → R a b → l11 a c ≡ l11 b c
      l12 a b c r = ΣPathP ((eq/ _ _ (l121 a b r _)) , refl) where
        l121 : ∀ a b → (r : R a b) → ∀ f → R (thom f a) (thom f b)
        l121 .(x · (y · z)) .((x · y) · z) (assoc x y z) f = assoc _ _ _
        l121 .(b · ε) b (rid .b) f = rid _
        l121 .(x · y) .(y · x) (comm x y) f = comm _ _
        l121 .(_ · c) .(_ · c) (·c c r) f = ·c _ (l121 _ _ r f)

      l13 : (c : Tree ⟨ DWM ⟩) → (a b : Tree ⟨ DWA ⟩) → R a b → l11 c a ≡ l11 c b
      l13 c a b r = ΣPathP (refl , (eq/ _ _ (l131 a b r _))) where
        l131 : ∀ a b → (r : R a b) → ∀ f → R (thom f a) (thom f b)
        l131 .(x · (y · z)) .((x · y) · z) (assoc x y z) f = assoc _ _ _
        l131 .(b · ε) b (rid .b) f = rid _
        l131 .(x · y) .(y · x) (comm x y) f = comm _ _
        l131 .(_ · c) .(_ · c) (·c c r) f = ·c _ (l131 _ _ r f)

      l14 = rec2 (isSetΣ squash/ (λ _ → squash/)) l11 l12 l13 x y
    l1 (ƛ_ {B} f) = ƛ (λ x → l1 (f x))
    l1 (e1 ∪ e2) = l1 e1 ∪ l1 e2
    l1 (e1 · e2) = l1 e1 · l1 e2

    l12 : (a b : WMB.Bree) → WMB.S a b → QMB.S (l1 a) (l1 b)
    l12 .(x WMB.∪ y WMB.∪ z) .((x WMB.∪ y) WMB.∪ z) (assoc x y z) = assoc _ _ _
    l12 .(b WMB.∪ WMB.∅) b (rid .b) = rid _
    l12 .(x WMB.∪ y) .(y WMB.∪ x) (comm x y) = comm _ _
    l12 .(_ WMB.∪ c) .(_ WMB.∪ c) (∪c c r) = ∪c _ (l12 _ _ r)
    l12 .(b WMB.∪ b) b (idem .b) = idem _
    l12 .(x WMB.· y WMB.· z) .((x WMB.· y) WMB.· z) (assoc· x y z) = assoc· _ _ _
    l12 .(b WMB.· WMB.` Q.ε ·WCom) b (rid· .b) = rid· _
    l12 .(_ WMB.· c) .(_ WMB.· c) (·c c r) = ·c _ (l12 _ _ r)
    l12 .(x WMB.· y) .(y WMB.· x) (comm· x y) = comm· _ _
    l12 .(x WMB.· WMB.∅) .WMB.∅ (def∅· x) = def∅· _
    l12 .(WMB.` (x1 , x2) WMB.· WMB.` (y1 , y2)) .(WMB.` (·WCom Q.· (x1 , x2)) (y1 , y2)) (def· (x1 , x2) (y1 , y2)) = J (λ y eq → QMB.S (QMB.` L1.l14 x1 x2 QMB.· QMB.` L1.l14 y1 y2)
     (QMB.` y)) (def· _ _) (sym l121) where
      l121 : L1.l14 (x1 * y1) (x2 * y2) ≡ (L1.l14 x1 x2) QMB.Q.· (L1.l14 y1 y2)
      l121 = elimProp4 {P = λ x1 y1 x2 y2 → L1.l14 (x1 * y1) (x2 * y2) ≡ (L1.l14 x1 x2) QMB.Q.· (L1.l14 y1 y2)}
               (λ x y z t → isSetΣ squash/ (λ _ → squash/) _ _) (λ a b c d → refl) x1 y1 x2 y2
    l12 .(x WMB.· (WMB.ƛ y)) .(WMB.ƛ (λ q → x WMB.· y q)) (defƛ· x y) = defƛ· _ _
    l12 .(x WMB.· (y WMB.∪ z)) .(x WMB.· y WMB.∪ x WMB.· z) (dist` x y z) = dist` _ _ _
    l12 .(WMB.ƛ (λ c → x c WMB.∪ y c)) .((WMB.ƛ x) WMB.∪ (WMB.ƛ y)) (distƛ∪ x y) = distƛ∪ _ _
    l12 .(WMB.ƛ (λ c → x c WMB.· y c)) .((WMB.ƛ x) WMB.· (WMB.ƛ y)) (distƛ· x y) = distƛ· _ _
    l12 .(WMB.ƛ y) b (remƛ .b y eq) = remƛ _ _ λ i z → l1 (eq i z)
    l12 .(WMB.ƛ _) .(WMB.ƛ _) (ƛS f) = ƛS λ c → l12 _ _ (f c)
    
--   qq : (WM → QM) → (WA → QA) → ⟨ WR ⟩ → ⟨ QR ⟩
--   qq f g x = rec QSRI.is-set {!WA!} {!!} x where
--     l1 : WMB.Bree → ⟨ QR ⟩
--     l1 ∅       = QSR.0r
--     l1 (` (x , y))   = {!!}
--     l1 (ƛ x)   = [ ƛ (λ q → {!x q!}) ]
--     l1 (x ∪ y) = (l1 x) QSR.+ l1 y
--     l1 (x · y) = (l1 x) QSR.⋆ l1 y


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


