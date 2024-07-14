{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (rec)
open import MLTT.List
open import MLTT.Maybe
open import MLTT.Vector
open import UF.Subsingletons
open import Naturals.Order
open import UF.FunExt
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Notation.General
open import UF.Sets
open import UF.Base
open import UF.Embeddings

module Free where

module magma-structure (E : 𝓤 ̇) where

 T* = E → E → E

module _ (E : 𝓤 ̇)  where
 open magma-structure E

 magma-structure = T*

module magma-structure-names {E : 𝓤 ̇} (s : magma-structure E) where
 open magma-structure E

 _*_ : T*
 _*_ = s

module semigroup-axioms {E : 𝓤 ̇} (s : magma-structure E) where
 open magma-structure E
 open magma-structure-names s

 T*-assoc : 𝓤 ̇
 T*-assoc = ∀ a b c → a * (b * c) ＝ (a * b) * c

module _ {E : 𝓤 ̇} (s : magma-structure E) where
 open semigroup-axioms s

 semigroup-axioms = T*-assoc

module semigroup-axiom-names  {E : 𝓤 ̇} (s : magma-structure E) (ax : semigroup-axioms s) where
 open semigroup-axioms s

 *-assoc : T*-assoc
 *-assoc = ax

module monoid-structure (E : 𝓤 ̇ ) where
 open magma-structure E public

 Tid : 𝓤 ̇
 Tid = E

module _ (E : 𝓤 ̇) where

 open monoid-structure E

 monoid-structure : 𝓤 ̇
 monoid-structure = T* × Tid

module monoid-structure-names {E : 𝓤 ̇} (s : monoid-structure E) where
 open monoid-structure E
 open magma-structure-names (pr₁ s) public
  
 e : Tid
 e = pr₂ s

module monoid-axioms {E : 𝓤 ̇} (s : monoid-structure E) where
 open monoid-structure E
 open monoid-structure-names s
 open semigroup-axioms (pr₁ s) public

 T*-lid : 𝓤 ̇
 T*-lid = ∀ a → e * a ＝ a

 T*-rid : 𝓤 ̇
 T*-rid = ∀ a → a * e ＝ a

module _ {E : 𝓤 ̇} (s : monoid-structure E) where
 open monoid-axioms s
  
 monoid-axioms : 𝓤 ̇
 monoid-axioms = T*-assoc × T*-lid × T*-rid
  
module monoid-axiom-names {E : 𝓤 ̇} (ss : monoid-structure E) (s : monoid-axioms ss) where
 open monoid-structure E
 open monoid-axioms ss
 open semigroup-axiom-names (pr₁ ss) (pr₁ s) public

 *-lid : T*-lid
 *-lid = pr₁ (pr₂ s)
  
 *-rid : T*-rid
 *-rid = pr₂ (pr₂ s)

module comm-axioms {E : 𝓤 ̇} (s : magma-structure E) where
 open magma-structure E
 open magma-structure-names s
 open semigroup-axioms s public

 T*-comm : 𝓤 ̇
 T*-comm = ∀ a b → a * b ＝ b * a

module _ {E : 𝓤 ̇} (s : magma-structure E) where
 open magma-structure E
 open comm-axioms s

 comm-axioms : 𝓤 ̇
 comm-axioms = T*-assoc × T*-comm

module comm-axiom-names {E : 𝓤 ̇} (s : magma-structure E) (ax : comm-axioms s) where
 open comm-axioms s

 open semigroup-axiom-names s (pr₁ ax) public

 *-comm : T*-comm
 *-comm = pr₂ ax

module commonoid-axioms {E : 𝓤 ̇} (s : monoid-structure E) where
 open monoid-structure E
 open monoid-structure-names s
 open monoid-axioms s public
 open comm-axioms (pr₁ s) hiding (T*-assoc) public

module _ {E : 𝓤 ̇} (s : monoid-structure E) where
 open monoid-structure E
 open commonoid-axioms s

 commonoid-axioms : 𝓤 ̇
 commonoid-axioms = (T*-assoc × T*-lid × T*-rid) × T*-comm

module commonoid-axiom-names {E : 𝓤 ̇} (s : monoid-structure E) (ax : commonoid-axioms s) where
 open commonoid-axioms s

 open monoid-axiom-names s (pr₁ ax) public

 *-comm : T*-comm
 *-comm = pr₂ ax


record magma : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
 open magma-structure E public
 field
  str : magma-structure E
 open magma-structure-names str public

record semigroup : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
 open magma-structure E public
 field
  str : magma-structure E
 open semigroup-axioms str public
 field
  ax : semigroup-axioms str
 open magma-structure-names str public
 open semigroup-axiom-names str ax public

record comm-sgroup : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
 open magma-structure E public
 field
  str : magma-structure E 
 open comm-axioms str public
 field
  ax :  comm-axioms str
 open magma-structure-names str public
 open comm-axiom-names str ax public

module _ (m : comm-sgroup {𝓤}) where
 private
  module M = magma
  module C = comm-sgroup m

 comm-sgroup-is-magma : magma
 M.E comm-sgroup-is-magma = C.E
 M.str comm-sgroup-is-magma = C.str

module icomm-axioms {E : 𝓤 ̇} (s : magma-structure E) where
 open magma-structure-names s
 open comm-axioms s public

 T*-idem : 𝓤 ̇
 T*-idem = (a : E) → a * a ＝ a

module _ {E : 𝓤 ̇} (s : magma-structure E) where
 open magma-structure E
 open icomm-axioms s

 icomm-axioms : 𝓤 ̇
 icomm-axioms = comm-axioms s × T*-idem

module icomm-axiom-names {E : 𝓤 ̇} (s : magma-structure E) (ax : icomm-axioms s) where
 open icomm-axioms s

 open comm-axiom-names s (pr₁ ax) public

 *-idem : T*-idem
 *-idem = pr₂ ax

record icomm-sgroup : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
 open magma-structure E public
 field
  str : magma-structure E 
 open icomm-axioms str public
 field
  ax :  icomm-axioms str
 open magma-structure-names str public
 open icomm-axiom-names str ax public

module _ (m : icomm-sgroup {𝓤}) where
 private
  module M = magma
  module C = icomm-sgroup m

 icomm-sgroup-is-magma : magma
 M.E icomm-sgroup-is-magma = C.E
 M.str icomm-sgroup-is-magma = C.str


record monoid : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
  str : monoid-structure E
  ax : monoid-axioms str

 open monoid-structure public
 open monoid-structure-names str public
 open monoid-axioms str public
 open monoid-axiom-names str ax public

record commonoid : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
  str : monoid-structure E
  ax : commonoid-axioms str

 open monoid-structure public
 open monoid-structure-names str public
 open commonoid-axioms str public
 open commonoid-axiom-names str ax public


module _ (m : commonoid {𝓤}) where
 private
  module M = monoid
  module C = commonoid m

 commonoid-is-monoid : monoid
 monoid.E commonoid-is-monoid = C.E
 monoid.str commonoid-is-monoid = C.str
 monoid.ax commonoid-is-monoid = pr₁ C.ax


module icommonoid-axioms {E : 𝓤 ̇} (s : monoid-structure E) where
 open monoid-structure E
 open monoid-structure-names s
 open monoid-axioms s public
 open icomm-axioms (pr₁ s) hiding (T*-assoc) public

module _ {E : 𝓤 ̇} (s : monoid-structure E) where
 open monoid-structure E
 open icommonoid-axioms s

 icommonoid-axioms : 𝓤 ̇
 icommonoid-axioms = (T*-assoc × T*-lid × T*-rid) × T*-comm × T*-idem

module icommonoid-axiom-names {E : 𝓤 ̇} (s : monoid-structure E) (ax : icommonoid-axioms s) where
 open icommonoid-axioms s

 open monoid-axiom-names s (pr₁ ax) public

 *-comm : T*-comm
 *-comm = pr₁ (pr₂ ax)

 *-idem : T*-idem
 *-idem = pr₂ (pr₂ ax)

record icommonoid : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
  str : monoid-structure E
  ax : icommonoid-axioms str

 open monoid-structure public
 open monoid-structure-names str public
 open icommonoid-axioms str public
 open icommonoid-axiom-names str ax public

module _ (m : icommonoid {𝓤}) where
 private
  module M = monoid
  module C = icommonoid m

 icommonoid-is-monoid : monoid
 monoid.E icommonoid-is-monoid = C.E
 monoid.str icommonoid-is-monoid = C.str
 monoid.ax icommonoid-is-monoid = pr₁ C.ax



module homomorphism (s : magma {𝓤}) (v : magma {𝓤}) where
 private
  module S = magma s
  module V = magma v

 _is-hom : (f : S.E → V.E) → 𝓤 ̇
 f is-hom = ∀ a b → f (a S.* b) ＝ f a V.* f b


module free-universal (s : magma {𝓤}) {C : 𝓦 ̇} (`_ : C → magma.E s) where
 private
  module S = magma s
  open homomorphism s

 module _ (v : magma) where
  module V = magma v

  freeΔ : (``_ : C → V.E) → (f : (S.E → V.E)) → (𝓤 ⊔ 𝓦) ̇
  freeΔ ``_ f = _is-hom v f × (f ∘ `_ ＝ ``_)

 free-uni : (𝓤 ⁺ ⊔ 𝓦) ̇
 free-uni = (v : magma {𝓤}) → (``_ : C → _) → ∃! (freeΔ v ``_ )

record free-comm-sgroup {𝓤} (C : 𝓦 ̇ ) : (𝓤 ⁺) ⊔ 𝓦 ̇  where
 field
  r : comm-sgroup {𝓤}
 open comm-sgroup r public
 field
  `_ : C → E
  emb : is-embedding `_
 open free-universal (comm-sgroup-is-magma r) `_ public
 field
  univ : free-uni

record free-icomm-sgroup {𝓤} (C : 𝓦 ̇ ) : (𝓤 ⁺) ⊔ 𝓦 ̇  where
 field
  r : icomm-sgroup {𝓤}
 open icomm-sgroup r public
 field
  `_ : C → E
  emb : is-embedding `_
 open free-universal (icomm-sgroup-is-magma r) `_ public
 field
  univ : free-uni


module monoid-homomorphism (s : monoid {𝓤}) (v : monoid {𝓤}) where
 private
  module S = monoid s
  module V = monoid v

 _is-hom : (f : S.E → V.E) → 𝓤 ̇
 f is-hom = (∀ a b → f (a S.* b) ＝ f a V.* f b) × (f S.e ＝ V.e)

module monoid-homomorphism-trans (s : monoid {𝓤})  (v : monoid {𝓤}) (d : monoid {𝓤}) where
 private
  module S = monoid s
  module V = monoid v
  module D = monoid d
  module SV = monoid-homomorphism s v
  module VD = monoid-homomorphism v d
  module SD = monoid-homomorphism s d

 trans-hom : (g : V.E → D.E) → g VD.is-hom → (f : S.E → V.E) → f SV.is-hom → (g ∘ f) SD.is-hom
 pr₁ (trans-hom g g-is-hom f f-is-hom) a b = ap g (pr₁ f-is-hom a b) ∙ pr₁ g-is-hom _ _
 pr₂ (trans-hom g g-is-hom f f-is-hom) = ap g (pr₂ f-is-hom) ∙ pr₂ g-is-hom

module monoid-free-universal (s : monoid {𝓤}) {C : 𝓦 ̇} (`_ : C → monoid.E s) where
 private
  module S = monoid s
  open monoid-homomorphism s

 module _ (v : monoid) where
  module V = monoid v

  freeΔ : (``_ : C → V.E) → (f : (S.E → V.E)) → (𝓤 ⊔ 𝓦) ̇
  freeΔ ``_ f = _is-hom v f × (f ∘ `_ ＝ ``_)

 free-uni : (𝓤 ⁺ ⊔ 𝓦) ̇
 free-uni = (v : monoid {𝓤}) → (``_ : C → _) → ∃! (freeΔ v ``_ )

record free-commonoid {𝓤} (C : 𝓦 ̇ ) : (𝓤 ⁺) ⊔ 𝓦 ̇  where
 field
  r : commonoid {𝓤}
 open commonoid r public
 field
  `_ : C → E
  emb : is-embedding `_
 open monoid-free-universal (commonoid-is-monoid r) `_ public
 field
  univ : free-uni

record free-icommonoid {𝓤} (C : 𝓦 ̇ ) : (𝓤 ⁺) ⊔ 𝓦 ̇  where
 field
  r : icommonoid {𝓤}
 open icommonoid r public
 field
  `_ : C → E
  emb : is-embedding `_
 open monoid-free-universal (icommonoid-is-monoid r) `_ public
 field
  univ : free-uni


module magma-ring-structure (E : 𝓤 ̇) where
 module S＋ = magma-structure E
 module S· = magma-structure E

module _ (E : 𝓤 ̇) where
 open magma-ring-structure E

 magma-ring-structure : 𝓤 ̇
 magma-ring-structure = S＋.T* × S·.T*
 

module magma-ring-structure-names {E : 𝓤 ̇} (s : magma-ring-structure E) where
 open magma-ring-structure E

 _＋_ : S＋.T*
 _＋_ = pr₁ s

 _·_ : S·.T*
 _·_ = pr₂ s

module magma-ring-axioms {E : 𝓤 ̇} (s : magma-ring-structure E) where
 open magma-ring-structure E
 open magma-ring-structure-names s

 T·-distr : 𝓤 ̇
 T·-distr = (a b c : E) → a · (b ＋ c) ＝ (a · b) ＋ (a · c)

module _  {E : 𝓤 ̇} (s : magma-ring-structure E) where
 open magma-ring-axioms s
 
 module magma-ring-axiom-names (ax : T·-distr) where
  open magma-ring-structure E
  open magma-ring-structure-names s
  
  ·-distr : T·-distr
  ·-distr = ax
 
record magma-ring : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
  str : magma-ring-structure E
 open magma-ring-axioms str public
 field
  ax : T·-distr
 open magma-ring-structure E public
 open magma-ring-structure-names str public
 open magma-ring-axiom-names str ax public

module _ (m : magma-ring {𝓤}) where
 private
  module M = magma
  module R = magma-ring m

 ring-is-+-magma : magma
 M.E ring-is-+-magma = R.E
 M.str ring-is-+-magma = R._＋_

 ring-is-·-magma : magma
 M.E ring-is-·-magma = R.E
 M.str ring-is-·-magma = R._·_

module free-ring-universal (s : magma-ring {𝓤}) (open magma-ring s) {C : 𝓦 ̇} (`_ : C → E) where
 private
  module S = magma-ring s

 module _ (v : magma-ring) where
  private
   module V = magma-ring v
   module H+ = homomorphism (ring-is-+-magma s) (ring-is-+-magma v)
   module H· = homomorphism (ring-is-·-magma s) (ring-is-·-magma v)
  
  free-ringΔ : (``_ : C → V.E) → (f : (S.E → V.E)) → (𝓤 ⊔ 𝓦) ̇
  free-ringΔ ``_ f = f H+.is-hom × f H·.is-hom × (f ∘ `_ ＝ ``_)
  
 free-ring-uni : (𝓤 ⁺ ⊔ 𝓦) ̇
 free-ring-uni = (v : magma-ring) → (``_ : C → _) → ∃! (free-ringΔ v ``_)

-- idem-comm-semi-ring
module icsring-structure (E : 𝓤 ̇) where
 open magma-ring-structure E public

module _ (E : 𝓤 ̇) where
 open icsring-structure E

 icsring-structure : 𝓤 ̇
 icsring-structure = S＋.T* × S·.T*

module icsring-structure-names {E : 𝓤 ̇} (s : icsring-structure E) where
 open icsring-structure E

 _＋_ : S＋.T*
 _＋_ = pr₁ s

 _·_ : S·.T*
 _·_ = pr₂ s


module icsring-axioms {E : 𝓤 ̇} (s : icsring-structure E) where
 open icsring-structure E
 open icsring-structure-names s

 open magma-ring-axioms s public
 module A＋ = comm-axioms _＋_
 module A· = comm-axioms _·_

 T＋-idem : 𝓤 ̇
 T＋-idem = (a : E) → a ＋ a ＝ a


module _ {E : 𝓤 ̇} (s : icsring-structure E) where
 open icsring-structure E
 open icsring-structure-names s
 open icsring-axioms s

 icsring-axioms : 𝓤 ̇
 icsring-axioms = comm-axioms _＋_ × comm-axioms _·_ × T·-distr × T＋-idem

module icsring-axiom-names {E : 𝓤 ̇} (s : icsring-structure E) (ax : icsring-axioms s) where
 open icsring-structure E
 open icsring-structure-names s
 open icsring-axioms s

 module AN＋ = comm-axiom-names _＋_ (pr₁ ax)
 module AN· = comm-axiom-names _·_ (pr₁ (pr₂ ax))
 open magma-ring-axiom-names s (pr₁ (pr₂ (pr₂ ax))) public

 ＋-idem : T＋-idem
 ＋-idem = pr₂ (pr₂ (pr₂ ax))

record icsring : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
  str : icsring-structure E
  ax : icsring-axioms str

 open icsring-structure public
 open icsring-structure-names str public
 open icsring-axioms str public
 open icsring-axiom-names str ax public

module _ (m : icsring {𝓤}) where
 private
  module M = magma-ring
  module R = icsring m

 icsring-is-magma-ring : magma-ring
 M.E icsring-is-magma-ring = R.E
 M.str icsring-is-magma-ring = R.str
 M.ax icsring-is-magma-ring = R.·-distr

module _ (m : icsring {𝓤}) where
 private
  module M = icomm-sgroup {𝓤}
  module R = icsring m

 icsring-is-icomm-sgroup : icomm-sgroup
 icomm-sgroup.E icsring-is-icomm-sgroup = R.E
 icomm-sgroup.str icsring-is-icomm-sgroup = R._＋_
 pr₁ (icomm-sgroup.ax icsring-is-icomm-sgroup) = pr₁ R.ax
 pr₂ (icomm-sgroup.ax icsring-is-icomm-sgroup) = R.＋-idem

record free-icsring (C : 𝓦 ̇ ) : (𝓤 ⁺) ⊔ 𝓦 ̇  where
 field
  r : icsring {𝓤}
 open icsring r public
 field
  `_ : C → E
  emb : is-embedding `_
 open free-ring-universal (icsring-is-magma-ring r) `_ public
 field
  univ : free-ring-uni




module icring-structure (E : 𝓤 ̇) where
 module S＋ = monoid-structure E
 module S· = magma-structure E

module _ (E : 𝓤 ̇) where
 open icring-structure E

 icring-structure : 𝓤 ̇
 icring-structure = (S＋.T* × S＋.Tid) × S·.T*

module icring-structure-names {E : 𝓤 ̇} (s : icring-structure E) where
 open icring-structure E

 _＋_ : S＋.T*
 _＋_ = pr₁ (pr₁ s)

 _·_ : S·.T*
 _·_ = pr₂ s

 e : S＋.Tid
 e = pr₂ (pr₁ s)

module icring-axioms {E : 𝓤 ̇} (s : icring-structure E) where
 open icring-structure E
 open icring-structure-names s

 open magma-ring-axioms (pr₁ (pr₁ s) , pr₂ s) public
 module A＋ = icommonoid-axioms (pr₁ s)
 module A· = comm-axioms _·_

module _ {E : 𝓤 ̇} (s : icring-structure E) where
 open icring-structure E
 open icring-structure-names s
 open icring-axioms s

 icring-axioms : 𝓤 ̇
 icring-axioms = icommonoid-axioms (pr₁ s) × comm-axioms _·_ × T·-distr

module icring-axiom-names {E : 𝓤 ̇} (s : icring-structure E) (ax : icring-axioms s) where
 open icring-structure E
 open icring-structure-names s
 open icring-axioms s

 module AN＋ = icommonoid-axiom-names (pr₁ s) (pr₁ ax)
 module AN· = comm-axiom-names _·_ (pr₁ (pr₂ ax))
 open magma-ring-axiom-names (pr₁ (pr₁ s) , pr₂ s) (pr₂ (pr₂ ax)) public

record icring : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
  str : icring-structure E
  ax : icring-axioms str

 open icring-structure public
 open icring-structure-names str public
 open icring-axioms str public
 open icring-axiom-names str ax public

module _ (m : icring {𝓤}) where
 private
  module M = icommonoid {𝓤}
  module R = icring m

 icring-is-icommonoid : icommonoid
 icommonoid.E icring-is-icommonoid = R.E
 icommonoid.str icring-is-icommonoid = pr₁ R.str
 icommonoid.ax icring-is-icommonoid = pr₁ R.ax

 private
  module E = icommonoid {𝓤}

 icring-is-·-magma : magma
 magma.E icring-is-·-magma = R.E
 magma.str icring-is-·-magma = R._·_



module free-icring-universal (s : icring {𝓤}) (open icring s) {C : 𝓦 ̇} (`_ : C → E) where
 private
  module S = icring s

 module _ (v : icring) where
  private
   module V = icring v
   module H+ = monoid-homomorphism (icommonoid-is-monoid (icring-is-icommonoid s)) (icommonoid-is-monoid (icring-is-icommonoid v))
   module H· = homomorphism (icring-is-·-magma s) (icring-is-·-magma v)
  
  free-ringΔ : (``_ : C → V.E) → (f : (S.E → V.E)) → (𝓤 ⊔ 𝓦) ̇
  free-ringΔ ``_ f = f H+.is-hom × f H·.is-hom × (f ∘ `_ ＝ ``_)
  
 free-ring-uni : (𝓤 ⁺ ⊔ 𝓦) ̇
 free-ring-uni = (v : icring) → (``_ : C → _) → ∃! (free-ringΔ v ``_)

record free-icring (C : 𝓦 ̇ ) : (𝓤 ⁺) ⊔ 𝓦 ̇  where
 field
  r : icring {𝓤}
 open icring r public
 field
  `_ : C → E
  emb : is-embedding `_
 open free-icring-universal r `_ public
 field
  univ : free-ring-uni
