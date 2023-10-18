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
open import MLTT.Two renaming (₀ to ⇒ ; ₁ to ⇐)

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
   
record magma : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
 open magma-structure E public
 field
  str :  T*
 open magma-structure-names str public

record semigroup : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
 open magma-structure E public
 field
  str :  T*
 open semigroup-axioms str public
 field
  ax :  T*-assoc
 open magma-structure-names str public
 open semigroup-axiom-names str ax public

record comm-sgroup : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
 open magma-structure E public
 field
  str :  T*
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



record monoid : 𝓤 ⁺ ̇  where
 field
  E : 𝓤 ̇
  str : monoid-structure E
  ax : monoid-axioms str

 open monoid-structure public
 open monoid-structure-names str public
 open monoid-axioms str public
 open monoid-axiom-names str ax public

module homomorphism (s : magma {𝓤}) (v : magma {𝓥}) where
 private
  module S = magma s
  module V = magma v

 module _ (f : S.E → V.E) where

  _is-hom : (𝓤 ⊔ 𝓥) ̇
  _is-hom = ∀ a b → f (a S.* b) ＝ f a V.* f b


module free-universal (s : magma {𝓤}) {C : 𝓦 ̇} (open magma s) (`_ : C → E) where
 private
  module S = magma s
 module _ (v : magma {𝓥})  where
  module V = magma v
  open homomorphism s v
  
  free-uni : (𝓤 ⊔ 𝓦 ⊔ 𝓥) ̇
  free-uni = (``_ : C → V.E) → Σ f ꞉ (S.E → V.E) , f is-hom × (f ∘ `_ ＝ ``_) 


free-comm-sgroup-uni : (r : comm-sgroup {𝓤}) → {C : 𝓦 ̇} → (open comm-sgroup r) (`_ : C → E) → 𝓤ω
free-comm-sgroup-uni r `_ = ∀ 𝓥 → (q : comm-sgroup {𝓥}) → free-universal.free-uni (comm-sgroup-is-magma r) `_ (comm-sgroup-is-magma q)


record free-comm-sgroup (C : 𝓦 ̇ ) : 𝓤ω where
 field
  {u} : _
  r : comm-sgroup {u}
 open comm-sgroup r public
 field
  `_ : C → E
  emb : is-embedding `_
  univ : free-comm-sgroup-uni r `_



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
 module _  (v : magma-ring {𝓥}) where
  private
   module V = magma-ring v
   module H+ = homomorphism (ring-is-+-magma s) (ring-is-+-magma v)
   module H· = homomorphism (ring-is-·-magma s) (ring-is-·-magma v)
  
  free-ring-uni : (𝓤 ⊔ 𝓦 ⊔ 𝓥) ̇
  free-ring-uni = (``_ : C → V.E) → Σ f ꞉ (S.E → V.E) , f H+.is-hom × f H·.is-hom × (f ∘ `_ ＝ ``_) 

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


module free-icsring-universal {𝓤} {𝓦} (m : icsring {𝓤}) (open icsring m) {C : 𝓦 ̇} (`_ : C → E) = free-ring-universal {𝓤} (icsring-is-magma-ring m) {C} (`_) 

free-icsring-uni : (r : icsring {𝓤}) → {C : 𝓦 ̇} → (open icsring r) (`_ : C → E) → 𝓤ω
free-icsring-uni r `_ = ∀ 𝓥 → (q : icsring {𝓥}) → free-icsring-universal.free-ring-uni r `_ (icsring-is-magma-ring q)

record free-icsring (C : 𝓤 ̇  → 𝓦 ̇ ) : 𝓤ω where
 field
  r : icsring
 open icsring r public
 field
  `_ : C E → E
  emb : is-embedding `_
  univ : free-icsring-uni r `_
