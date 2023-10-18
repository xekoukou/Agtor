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
open import MLTT.Two renaming (₀ to ⇒ ; ₁ to ⇐)

module SType  (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓥 ̇ ) where

open import BSet fe pt Msg

open BSet

module structure-statements (C : 𝓤 ̇) (E : 𝓤 ̇) where

 T⃗ : 𝓤 ̇ 
 T⃗ = C → E

 T⃖ : 𝓤 ̇
 T⃖ = C → E

 T& : 𝓤 ̇
 T& = E → E → E

 T∣ : 𝓤 ̇
 T∣ = E → E → E

  
module _ (C : 𝓤 ̇) (E : 𝓤 ̇) where
 open structure-statements C E

 structure : 𝓤 ̇
 structure = T⃗ × T⃖ × T& × T∣


module structure-names {C : 𝓤 ̇} {E : 𝓤 ̇ } (str : structure C E) where
 open structure-statements C E

 _⃗ : T⃗
 _⃗ = pr₁ str
  
 _⃖ : T⃖
 _⃖ = pr₁ (pr₂ str)

 _&_ : T&
 _&_ = pr₁ (pr₂ (pr₂ str))

 _∣_ : T∣
 _∣_ = pr₂ (pr₂ (pr₂ str))


module axiom-statements {C : 𝓤 ̇} {E : 𝓤 ̇ } (str : structure C E) where
 open structure-statements C E
 open structure-names str

 T&-distr : 𝓤 ̇
 T&-distr = (a b c : E) → a & (b ∣ c) ＝ (a & b) ∣ (a & c)

 T&-comm : 𝓤 ̇
 T&-comm = (a b : E) → a & b ＝ b & a
  
 T∣-comm : 𝓤 ̇
 T∣-comm = (a b : E) → a ∣ b ＝ b ∣ a

 T∣-idem : 𝓤 ̇
 T∣-idem = (a : E) → a ∣ a ＝ a


module _ {C : 𝓤 ̇} {E : 𝓤 ̇ } (str : structure C E) where
 open structure-statements C E
 open structure-names str
 open axiom-statements str

 axioms : 𝓤 ̇  
 axioms = T&-distr × T&-comm × T∣-comm × T∣-idem

module axiom-names {C : 𝓤 ̇ } {E : 𝓤 ̇ } {str : structure C E} (ax : axioms str) where
 open axiom-statements str

 &-distr : T&-distr
 &-distr = pr₁ ax
  
 &-comm : T&-comm
 &-comm = pr₁ (pr₂ ax)

 ∣-comm : T∣-comm
 ∣-comm = pr₁ (pr₂ (pr₂ ax))

 ∣-idem : T∣-idem
 ∣-idem = pr₂ (pr₂ (pr₂ ax))


module _ (C : 𝓤 ̇) (E : 𝓤 ̇ ) where

 𝟚C-semi : 𝓤 ̇
 𝟚C-semi = Σ str ꞉ structure C E , axioms str


record 𝟚C-Semi (C : 𝓤 ̇  → 𝓤 ̇) : 𝓤 ⁺ ̇  where
 field
  O : 𝓤 ̇ 
  str : structure (C O) O
  ax : axioms str
 open structure-statements O public
 open structure-names str public
 open axiom-statements str public
 open axiom-names {str = str} ax public
 field
 -- eliminator should be for any universe
  elim : {C : O → 𝓤 ̇}
     → (c→ : ∀ A → C (A ⃗))
     → (c← : ∀ A → C (A ⃖))
     → (_c&_ : (a : Σ C) → (b : Σ C) → C (pr₁ a & pr₁ b))
     → (_c∣_ : (a : Σ C) → (b : Σ C) → C (pr₁ a ∣ pr₁ b))
     → (c&-distr : 
        (a : Σ C) → (b : Σ C) → (c : Σ C)
        → a c& (_ , b c∣ c)              ＝ transport C ((&-distr (pr₁ a) (pr₁ b) (pr₁ c)) ⁻¹)
          ((_ , a c& b) c∣ (_ , a c& c)))
     → (c&-comm :(a : Σ C) → (b : Σ C)
        → a c& b                         ＝ transport C (&-comm (pr₁ b) (pr₁ a))
          (b c& a))
     → (c∣-comm :(a : Σ C) → (b : Σ C)
       → a c∣ b ＝ transport C (∣-comm (pr₁ b) (pr₁ a))
         (b c∣ a))
     → (c∣-idem : (a : Σ C)
       → a c∣ a ＝ transport C ((∣-idem (pr₁ a)) ⁻¹)
         (pr₂ a))
     → (x : O) → C x

 rec : {D : 𝓤 ̇}
     → (c→ : C O → D)
     → (c← : C O → D)
     → (_c&_ : (a : O × D) → (b : O × D) → D)
     → (_c∣_ : (a : O × D) → (b : O × D) → D)
     → (c&-distr : 
        (a : O × D) → (b : O × D) → (c : O × D)
        → a c& (pr₁ b ∣ pr₁ c , b c∣ c)              ＝
          ((pr₁ a & pr₁ b , a c& b) c∣ (pr₁ a & pr₁ c , a c& c)))
     → (c&-comm :(a : O × D) → (b : O × D)
        → a c& b                         ＝
          (b c& a))
     → (c∣-comm :(a : O × D) → (b : O × D)
       → a c∣ b ＝ 
         (b c∣ a))
     → (c∣-idem : (a : O × D)
       → a c∣ a ＝
         (pr₂ a))
     → (x : O) → D
 rec c→ c← _c&_ _c∣_ c&-distr c&-comm c∣-comm c∣-idem x
  = elim
     c→
     c←
     _c&_
     _c∣_
     l1 l2 l3 l4 x where
      l1 : (a b c : Σ (λ v → _)) →
       (a c& ((pr₁ b ∣ pr₁ c) , (b c∣ c))) ＝
       transport (λ v → _) (&-distr (pr₁ a) (pr₁ b) (pr₁ c) ⁻¹)
       (((pr₁ a & pr₁ b) , (a c& b)) c∣ ((pr₁ a & pr₁ c) , (a c& c)))
      l1 (a , ac) (b , bc) (c , cc) with a & (b ∣ c) | &-distr a b c ⁻¹
      ... | _ | refl = c&-distr (a , ac) (b , bc) (c , cc)
      l2 : (a b : Σ (λ v → _)) →
       (a c& b) ＝ transport (λ v → _) (&-comm (pr₁ b) (pr₁ a)) (b c& a)
      l2 (a , ac) (b , bc) with (a & b) | &-comm b a
      ... | _ | refl = c&-comm (a , ac) (b , bc)
      l3 : (a b : Σ (λ v → _)) →
       (a c∣ b) ＝ transport (λ v → _) (∣-comm (pr₁ b) (pr₁ a)) (b c∣ a)
      l3 (a , ac) (b , bc) with (a ∣ b) | ∣-comm b a
      ... | _ | refl = c∣-comm (a , ac) (b , bc)
      l4 : (a : Σ (λ v → _)) →
       (a c∣ a) ＝ transport (λ v → _) (∣-idem (pr₁ a) ⁻¹) (pr₂ a)
      l4 (a , ac) with a ∣ a | ∣-idem a
      ... | _ | refl = c∣-idem (a , ac)
 
OpSet = 𝟚C-Semi (λ _ → BSet)

module OpSet (d : 𝟚C-Semi (λ _ → BSet)) = 𝟚C-Semi d

module Context {𝓤 𝓥} (Secret : 𝓤 ̇) where

-- TODO Secrets are unique ??? Hey, we dont need this because we perform the construction ??

 data Ctx (k : ℕ) : 𝓤 ⁺ ̇  where
  `ᶜ : (Vector Secret k → 𝓤 ̇ ) → Ctx k
  _∶ᶜ_ : (X : 𝓤 ̇ ) → (X → Ctx k) → Ctx k

 Vars : ∀{k} → (secrets : Vector Secret k) → Ctx k → 𝓤 ̇
 Vars secrets (`ᶜ X) = X secrets
 Vars secrets (X ∶ᶜ XS) = Σ (λ vl → Vars secrets (XS vl))

 Open : (C : 𝓥 ̇ ) → (Σ λ k → (Vector Secret k) × Ctx k)
      → (𝓤 ⊔ 𝓥)̇ 
 Open  C (k , (secrets , ctx)) = Vars secrets ctx → C

 OpenΣ : (C : 𝓥 ̇) → (𝓤 ⁺ ⊔ 𝓥) ̇
 OpenΣ C = Σ (Open C)

module _ (Secret : 𝓥 ̇) where

 open Context {𝓥} {𝓥 ⁺} Secret

 ParticleT : (C : 𝓥 ⁺ ̇) → 𝓥 ⁺ ̇
 ParticleT C = Σ A ꞉ BSet , Maybe ((mp : Msg) → { ⟨ A ⟩ mp } → C)

 SystemT = 𝟚C-Semi (λ A → ParticleT (OpenΣ A))

 module SystemT (d : SystemT) = 𝟚C-Semi d

module Proj (w : OpSet) (Secret : 𝓥 ̇) (e : SystemT Secret) where

 private
  module O = OpSet w
  module S = SystemT Secret e

 proj : S.O → O.O
 proj x = S.rec
  (λ { (BS , _) → BS O.⃗})
  (λ { (BS , _) → BS O.⃖})
  (λ a b → pr₂ a O.& pr₂ b)
  (λ a b → pr₂ a O.∣ pr₂ b)
  l1 l2 l3 l4 x where
    l1 : (a b c : Σ (λ v → O.O)) →
     (pr₂ a O.& (pr₂ b O.∣ pr₂ c)) ＝
     ((pr₂ a O.& pr₂ b) O.∣ (pr₂ a O.& pr₂ c))
    l1 (a , ac) (b , bc) (c , cc) = O.&-distr ac bc cc
    l2 : (a b : Σ (λ v → O.O)) →
     (pr₂ a O.& pr₂ b) ＝ (pr₂ b O.& pr₂ a)
    l2 (a , ac) (b , bc) = O.&-comm ac bc
    l3 : (a b : Σ (λ v → O.O)) →
     (pr₂ a O.∣ pr₂ b) ＝ (pr₂ b O.∣ pr₂ a)
    l3 (a , ac) (b , bc) = O.∣-comm ac bc
    l4 : (a : Σ (λ v → O.O)) →
     (pr₂ a O.∣ pr₂ a) ＝ pr₂ a
    l4 (a , ac) = O.∣-idem ac


module Value (w : OpSet) (Secret : 𝓥 ̇) (e : SystemT Secret) where

 private
  module O = OpSet w
  module S = SystemT Secret e



semilist-structure : ∀{𝓤} → 𝓤 ̇  → 𝓤 ̇  → 𝓤 ̇
semilist-structure X A = (X → X → X) × (A → X)


semilist-axioms : ∀{𝓤} → (X : 𝓤 ̇ ) → (A : 𝓤 ̇) → semilist-structure X A → 𝓤 ̇
semilist-axioms X A str@(_·_ , _) = -- is-set X
                                 commutative     _·_
                               × associative     _·_
                               × (∀ a → a ＝ a · a)

semilist : ∀{𝓤} → 𝓤 ̇ → 𝓤 ̇  → 𝓤 ̇
semilist X A = Σ (semilist-axioms X A)

module semilist-structure-names {𝓤} {X : 𝓤 ̇} {A : 𝓤 ̇} (str : semilist-structure X A) where

 _*_ : X → X → X
 _*_ = pr₁ str

 `_ : A → X
 `_ = pr₂ str

 module semilist-axiom-names (ax : semilist-axioms _ _ str) where

  *-comm : commutative _*_
  *-comm = pr₁ ax

  *-assoc : associative _*_
  *-assoc = pr₁ (pr₂ ax)

  *-idem : ∀ a → a ＝ a * a
  *-idem = pr₂ (pr₂ ax)

record Semilist {𝓤} (A : 𝓤 ̇ ) : 𝓤 ⁺ ̇  where
 field
  X : 𝓤 ̇
  mstr : semilist-structure X A
  mmax : semilist-axioms _ _ mstr

 open semilist-structure-names mstr public
 open semilist-axiom-names mmax public
 field
  elim : {C : X → 𝓤 ̇}
       → (c` : (x : A) → C (` x))
       → (_c*_ : (a b : Σ C) → let xa = pr₁ a
                                   xb = pr₁ b
                               in C (xa * xb))
       → (c*-comm : (a b : Σ C) → a c* b ＝ transport C (*-comm _ _) (b c* a))
       → (c*-assoc : (a b c : Σ C) → a c* (_ , b c* c) ＝ transport C (*-assoc _ _ _) ((_ , a c* b) c* c))
       → (C*-idem : (a : Σ C) → a c* a ＝ transport C (*-idem _) (pr₂ a))
       → (x : X) → C x
 rec : {C : 𝓤 ̇}
       → (c` : (x : A) → C)
       → (_c*_ : (a b : X × C) → C)
       → (c*-comm : (a b : X × C) → a c* b ＝ b c* a)
       → (c*-assoc : (a b c : X × C) → a c* (pr₁ b * pr₁ c , b c* c) ＝ (pr₁ a * pr₁ b , a c* b) c* c)
       → (C*-idem : (a : X × C) → a c* a ＝ pr₂ a)
       → (x : X) → C
 rec c` _c*_ c*-comm c*-assoc c*-idem
  = elim
     c`
     _c*_
     l1
     l2
     l3 where
      l1 : (a b : Σ (λ _ → _)) →
           (a c* b) ＝ transport (λ _ → _) (*-comm (pr₁ b) (pr₁ a)) (b c* a)
      l1 (a , ac) (b , bc) with b * a | *-comm b a
      ... | _ | refl = c*-comm (a , ac) (b , bc)
      l2 : (a b c : Σ (λ _ → _)) →
           (a c* ((pr₁ b * pr₁ c) , (b c* c))) ＝
           transport (λ _ → _) (*-assoc (pr₁ a) (pr₁ b) (pr₁ c))
           (((pr₁ a * pr₁ b) , (a c* b)) c* c)
      l2 (a , ac) (b , bc) (c , cc) with a * (b * c) | *-assoc a b c
      ... | _ | refl = c*-assoc (a , ac) (b , bc) (c , cc)
      l3 : (a : Σ (λ _ → _)) →
           (a c* a) ＝ transport (λ _ → _) (*-idem (pr₁ a)) (pr₂ a)
      l3 (a , ac) with a * a | *-idem a
      ... | _ | refl = c*-idem (a , ac)

-- To go from local properties to global ones, we need to generalize the function
-- from defining the change that happens when an actor gets a message,
-- to what happens to a system when an actor gets a message.
-- This new function is defined on a set of open sets instead of a single one.
-- We need predicates to be decidable.


module semilist-set where

 SemiLSet : 𝓥 ⁺⁺ ̇
 SemiLSet = Semilist (𝟚 × BSet)

 module SemiLSet (s : SemiLSet) = Semilist s
 
 module _ (s : SemiLSet) where
 
  open SemiLSet s
  
  _to-BSet : X → BSet × BSet
  x to-BSet
   = rec
      (λ { (⇒ , bs) → ⊥B , bs
         ; (⇐ , bs) → bs , ⊥B})
      (λ (_ , (a1 , a2)) (_ , (b1 , b2)) → (a1 || b1) , (a2 || b2))
      (λ { (_ , a1 , a2) (_ , b1 , b2) → {!!}})
      (λ (_ , a) (_ , b) (_ , c) → {!!})
      (λ (_ , (ac1 , ac2)) → {!!})
      x


module global-type-sheaf (Secret : 𝓥 ̇) (e : SystemT Secret) where

 open Context {𝓥} {𝓥 ⁺} Secret
 open SystemT Secret e

 SFunT : 𝓥 ⁺ ̇
 SFunT = 𝟚 × (Σ A ꞉ BSet , Maybe ((mp : Msg) → { ⟨ A ⟩ mp } → OpenΣ O))

 SheafT : 𝓥 ⁺⁺ ̇
 SheafT = Semilist SFunT

 module SheafT (s : SheafT) = Semilist s

module _ (w : OpSet) (open semilist-set) (s : SemiLSet) where
 
 open SemiLSet s hiding (rec)
 open OpSet w

 _to-semiLSet : O → X
 o to-semiLSet
  = rec
     (λ A → ` (⇒ , A))
     (λ A → ` (⇐ , A))
     (λ (_ , a) (_ , b) → a * b)
     (λ (_ , a) (_ , b) → a * b)
     {!!}
     {!!}
     {!!}
     {!!}
     o
    

module _ (Secret : 𝓥 ̇) (e : SystemT Secret) (open global-type-sheaf Secret e) (s : SheafT) where

 open SystemT Secret e
 open SheafT s renaming (rec to srec; elim to selim)

 -- TODO This is like the definition of a module
 -- where O is the ring and X is the module
 _*<_>_ : O → (_^_ : O → O → O) → X → X
 o *< _^_ > x
  = srec
     (λ { x@(d , BS , Nothing) → ` x
        ;   (d , BS , Just f) → ` (d , BS , Just λ mp {P} → let (ectx , g) = f mp {P} in ectx , λ v → o ^ g v)})
     (λ (_ , ac) (_ , bc) → ac * bc)
     {!!}
     {!!}
     {!!}
     x


 *<>-distr : (o : O) → (_^_ : O → O → O) → (a : X) → (b : X) → o *< _^_ > (a * b) ＝ (o *< _^_ > a) * (o *< _^_ > b)
 *<>-distr o _^_ a b
  = selim {C = λ a → o *< _^_ > (a * b) ＝ (o *< _^_ > a) * (o *< _^_ > b)}
    {!!}
    {!!}
    {!!}
    {!!}
    {!!}
    a

 _·ₘ_ : O → X → X
 o ·ₘ x = o *< _&_ > x 

 _to-sheafT : O → X
 x to-sheafT
  = rec
     (λ A → ` (⇒ , A))
     (λ A → ` (⇐ , A))
     (λ (a , ac) (b , bc) → (a ·ₘ bc) * (b ·ₘ ac))
     (λ (a , ac) (b , bc) → ac * bc)
     (λ (a , ac) (b , bc) (c , cc) → {!!})
     {!!}
     {!!}
     {!!}
     x

-- module _ (d : State) (open State d) (Vl : O → 𝓤 ̇ ) where

--  module value-structure-statements where
 
--   V⃗ : 𝓤 ⁺ ̇  
--   V⃗ = (mp : Msg) → ∀ A → ⦃ P : ⟨ A ⟩ mp ⦄ → Vl (A ⃗) 
 
--   V⃖ : 𝓤 ⁺ ̇  
--   V⃖ = ∀ A → Vl (A ⃖) 
 
--   V& : 𝓤 ⁺ ̇
--   V& = {X Y : O} → (x : Vl X) → (y : Vl Y) → Vl (X & Y)
 
--   V∣ : 𝓤 ⁺ ̇
--   V∣ = {X Y : O} → (x : Vl X) → (y : Vl Y) → Vl (X ∣ Y)

--  module _ where
--   open value-structure-statements
 
--   value-structure : (𝓤 ⁺) ⊔ (𝓤 ⁺) ̇
--   value-structure = V⃗ × V⃖ × V& × V∣
 
 
--  module value-structure-names (vl : value-structure) where
--   open value-structure-statements
 
--   _⃗∈_ : V⃗
--   _⃗∈_ = pr₁ vl
   
--   ⃖_ : V⃖
--   ⃖_ = pr₁ (pr₂ vl)
 
--   _＆_ : V&
--   _＆_ = pr₁ (pr₂ (pr₂ vl))
 
--   _∥_ : V∣
--   _∥_ = pr₂ (pr₂ (pr₂ vl))

--  module value-axiom-statements (vl : value-structure) where
--   open value-structure-statements
--   open value-structure-names vl

--   T∥-idem : (𝓤 ⁺)̇
--   T∥-idem = {A : O} → (a : Vl A) → (eq : A ＝ (A ∣ A)) → a ∥ a ＝ transport Vl eq a

--  -- these properties are derivable from the above.
--   T＆-distr : (𝓤 ⁺)̇
--   T＆-distr = {A B C : O} → (a : Vl A) → (b : Vl B) → (c : Vl C) → (eq : ((A & B) ∣ (A & C)) ＝ (A & (B ∣ C))) → a ＆ (b ∥ c) ＝ transport Vl eq ((a ＆ b) ∥ (a ＆ c))
 
--   T＆-comm : (𝓤 ⁺)̇
--   T＆-comm = {A B : O} → (a : Vl A) → (b : Vl B) → (eq : (B & A) ＝ (A & B)) → a ＆ b ＝ transport Vl eq (b ＆ a)
   
--   T∥-comm : (𝓤 ⁺)̇
--   T∥-comm = {A B : O} → (a : Vl A) → (b : Vl B) → (eq : (B ∣ A) ＝ (A ∣ B)) → a ∥ b ＝ transport Vl eq (b ∥ a)

--   record TVelim {＆-distr : T＆-distr} {＆-comm : T＆-comm} {∥-comm : T∥-comm} {∥-idem : T∥-idem}
--    : 𝓤 ⁺ ̇  where
--    field
--     f : {C : (o : O) → Vl o → 𝓤 ̇}
--         → (c→ : ∀ msg → ∀ A → ⦃ P : ⟨ A ⟩ msg ⦄ → C _ (msg ⃗∈ A))
--         → (c← : ∀ A → C _ ( ⃖ A))
--         → (_c&_ : ∀{oa ob} → (a : Σ (C oa)) → (b : Σ (C ob)) → let va = pr₁ a
--                                                                    vb = pr₁ b
--                                                                    in C _ (va ＆ vb))
--         → (_c∣_ : ∀{oa ob} → (a : Σ (C oa)) → (b : Σ (C ob)) → C _ (pr₁ a ∥ pr₁ b))

-- ----------------------------
--         → (c∥-idem : ∀{oa} → (a : Σ (C oa)) →
--           pr₂ a
--         ＝
--           transport
--            (λ o → (a : Σ (C oa)) → let va = pr₁ a in (oeq : o ＝ oa) → (vl : Vl o) → vl ＝ transport Vl (oeq ⁻¹) va → C _ vl)
--            (∣-idem oa)
--            (λ a oeq vl veq → let va = pr₁ a
--                              in transport (C _) (∥-idem va (oeq ⁻¹) ∙ veq ⁻¹) (a c∣ a)) a refl (pr₁ a) refl)
-- -------------------------
--         → (c&-distr : ∀{oa ob oc} →
--            (a : Σ (C oa)) → (b : Σ (C ob)) → (c : Σ (C oc))
--            →   a c& (_ , b c∣ c)
--              ＝
--                (transport (λ o → (a : Σ (C oa)) → let va = pr₁ a in (b : Σ (C ob)) → let vb = pr₁ b in (c : Σ (C oc)) → let vc = pr₁ c in (oeq : o ＝ (oa & (ob ∣ oc))) → (vl : Vl o) → vl ＝ transport Vl (oeq ⁻¹) (va ＆ (vb ∥ vc)) → C _ vl)
--                  (&-distr oa ob oc ⁻¹)
--                  λ a b c oeq vl veq → let va = pr₁ a
--                                           vb = pr₁ b
--                                           vc = pr₁ c
--                                       in transport (C _) ((ap (transport Vl (oeq ⁻¹)) (＆-distr va vb vc oeq) ∙ forth-and-back-transport oeq) ⁻¹ ∙ veq ⁻¹) ((_ , (a c& b)) c∣ (_ , a c& c))) a b c refl (pr₁ a ＆ (pr₁ b ∥ pr₁ c) ) refl)
-- ---------------------------
--         → (c∣-comm : ∀{oa ob} → (a : Σ (C oa)) → (b : Σ (C ob)) →
--           a c∣ b
--         ＝
--           transport
--            (λ o → (a : Σ (C oa)) → (b : Σ (C ob)) → let va = pr₁ a
--                                                         vb = pr₁ b
--                                                     in (oeq : o ＝ oa ∣ ob) → (vl : Vl o) → vl ＝ transport Vl (oeq ⁻¹) (va ∥ vb) → C _ vl)
--            (∣-comm ob oa)
--            (λ a b oeq vl veq → transport (C _) (∥-comm (pr₁ b) (pr₁ a) (oeq ⁻¹) ∙ veq ⁻¹) (b c∣ a))
--            a b refl (pr₁ a ∥ pr₁ b) refl)
-- ------------------------------
--         → (c&-comm : ∀{oa ob} → (a : Σ (C oa)) → (b : Σ (C ob)) →
--           a c& b
--         ＝
--           transport
--            (λ o → (a : Σ (C oa)) → (b : Σ (C ob)) → let va = pr₁ a
--                                                         vb = pr₁ b
--                                                     in (oeq : o ＝ oa & ob) → (vl : Vl o) → vl ＝ transport Vl (oeq ⁻¹) (va ＆ vb) → C _ vl)
--            (&-comm ob oa)
--            (λ a b oeq vl veq → transport (C _) (＆-comm (pr₁ b) (pr₁ a) (oeq ⁻¹) ∙ veq ⁻¹) (b c& a))
--            a b refl (pr₁ a ＆ pr₁ b) refl)
--       → {o : O} → (v : Vl o) → C _ v



--  module _ (vl : value-structure) where
--   open value-structure-statements
--   open value-structure-names vl 
--   open value-axiom-statements vl

--   value-axioms : 𝓤 ⁺ ⊔ 𝓤 ⁺ ̇  
--   value-axioms = T＆-distr × T＆-comm × T∥-comm × T∥-idem

--  module value-axiom-names {vstr : value-structure} (vax : value-axioms vstr) where
--   open value-axiom-statements vstr

--   ＆-distr : T＆-distr
--   ＆-distr = pr₁ vax

--   ＆-comm : T＆-comm
--   ＆-comm = pr₁ (pr₂ vax)

--   ∥-comm : T∥-comm
--   ∥-comm = pr₁ (pr₂ (pr₂ vax))

--   ∥-idem : T∥-idem
--   ∥-idem =  pr₂ (pr₂ (pr₂ vax))

--  vstate : 𝓤 ⁺ ̇
--  vstate = Σ vstr ꞉ value-structure , value-axioms vstr

-- module _ (d : State) (open State d) where
--  record VState : 𝓤 ⁺ ̇  where
--   field
--    Vl : O → 𝓤 ̇
--    vstr : value-structure d Vl
--    vax : value-axioms d Vl vstr

--   open value-structure-statements public
--   open value-structure-names d Vl vstr public
--   open value-axiom-statements d Vl vstr public
--   open value-axiom-names d Vl {vstr = vstr} vax public
--   field
--    elim : TVelim {＆-distr} {＆-comm} {∥-comm} {∥-idem}




-- module Context (Secret : 𝓤 ̇) where

-- -- TODO Secrets are unique ??? Hey, we dont need this because we perform the construction ??

--  data Ctx (k : ℕ) : 𝓤 ⁺ ̇  where
--   `ᶜ : (Vector Secret k → 𝓤 ̇ ) → Ctx k
--   _∶ᶜ_ : (X : 𝓤 ̇ ) → (X → Ctx k) → Ctx k

--  Vars : ∀{k} → (secrets : Vector Secret k) → Ctx k → 𝓤 ̇
--  Vars secrets (`ᶜ X) = X secrets
--  Vars secrets (X ∶ᶜ XS) = Σ (λ vl → Vars secrets (XS vl))

--  Open : (C : 𝓥 ̇ ) → (Σ λ k → (Vector Secret k) × Ctx k)
--       → (𝓤 ⊔ 𝓥)̇ 
--  Open  C (k , (secrets , ctx)) = Vars secrets ctx → C

--  OpenΣ : (C : 𝓥 ̇) → (𝓤 ⁺ ⊔ 𝓥) ̇
--  OpenΣ C = Σ (Open C)

-- module _ where

--  SFun : ∀{C : 𝓤 ⁺⁺ ̇} → 𝓤 ⁺⁺ ̇ 
--  SFun {C} = 𝟚 × (Σ A ꞉ BSet , ((mp : Msg) → { ⟨ A ⟩ mp } → C))
   

--  Sheaf : ∀ X C → (𝓤 ⁺⁺ ⁺) ̇
--  Sheaf X C = Semilist X (SFun {C})

-- module _ (Secret : 𝓤 ̇) (d : State) (open State d) (O→ : O → 𝓤 ⁺⁺ ̇ ) where

--  open Context Secret


--  module function-structure-statements where

--   F⃗ : 𝓤 ⁺⁺ ̇
--   F⃗ = (A : BSet) → ((mp : Msg) → { ⟨ A ⟩ mp } → OpenΣ (O + Σ O→)) → O→ (A ⃗)
 
--   F⃖ : 𝓤 ⁺⁺ ̇
--   F⃖ = (A : BSet) → ((mp : Msg) → { ⟨ A ⟩ mp } → OpenΣ (O + Σ O→)) → O→ (A ⃖)

--   F& : 𝓤 ⁺⁺ ̇ 
--   F& = ∀{A B} → (a : O→ A) → (b : O→ B) → O→ (A & B)
   
--   F∣ : 𝓤 ⁺⁺ ̇ 
--   F∣ = ∀{A B} → (a : O→ A) → (b : O→ B) → O→ (A ∣ B)

--  module _ where
--   open function-structure-statements
 
--   function-structure : 𝓤 ⁺⁺ ̇
--   function-structure = F⃗ × F⃖ × F& × F∣
 
 
--  module function-structure-names (str : function-structure) where
--   open function-structure-statements
 
--   _ᶠ⃗ : F⃗
--   _ᶠ⃗ = pr₁ str

--   _ᶠ⃖ : F⃖
--   _ᶠ⃖ = pr₁ (pr₂ str)

--   _&ᶠ_ : F&
--   _&ᶠ_ = pr₁ (pr₂ (pr₂ str))

--   _∣ᶠ_ : F∣
--   _∣ᶠ_ = pr₂ (pr₂ (pr₂ str))


--  record fstate : 𝓤 ⁺⁺ ̇  where
--   field
--    fstr : function-structure

--   open function-structure-statements public
--   open function-structure-names fstr public


--  module _ (fst : fstate) {X} (fmlt : Sheaf X (OpenΣ (O + Σ O→))) where
--   open Semilist fmlt

--   F⃗-to-Sheaf : (A : BSet) → ((mp : Msg) → { ⟨ A ⟩ mp } → OpenΣ (O + Σ O→)) → X
--   F⃗-to-Sheaf A x = ` (⇒ , (A , x ))

--   F⃖-to-Sheaf : (A : BSet) → ((mp : Msg) → { ⟨ A ⟩ mp } → OpenΣ (O + Σ O→)) → X
--   F⃖-to-Sheaf A x = ` (⇐ , (A , x ))

--   F&-to-Sheaf : ∀{A B} → (a : O→ A × X) → (b : O→ B × X) → X
--   F&-to-Sheaf (a , ax) (b , bx) =
--    (selim
--     (λ { (d , (BS , f)) → {!!}})
--     {!!}
--     {!!}
--     {!!}
--      bx)
--      *
--     {!!}

-- --   g : ∀ A → O→ A → X
-- --   g = {!!}

-- -- -- module _ (d : State) (v : VState d) (Secret : 𝓤 ̇) where
-- -- --  open Context Secret
-- -- --  open State d
-- -- --  open VState v

-- -- --  module _ (Type : ℕ → 𝓤 ̇) (Term : (k : ℕ) → Type k → 𝓤 ̇ ) (WQ : (x : Ctx) → (k : ℕ) → (Vars {x} → Σ (Term k)) → 𝓤 ̇) where

-- -- --   W : (x : Ctx) → (k : ℕ) → (Vars {x} → Σ (Term k)) → 𝓤 ̇
-- -- --   W x k B = WQ x k B
  
-- -- --   syntax W Γ k (λ vars → B) = [ vars ∈ Γ ] k ⊢ B

-- -- --   TOₜ : ℕ → 𝓤 ⁺ ̇   
-- -- --   TOₜ k = List (Σ (_≤ℕ k)) → O → Type k

-- -- --   TOₜ→Oₜ : ℕ → 𝓤 ⁺ ̇
-- -- --   TOₜ→Oₜ k = TOₜ k → (n : ℕ) → TOₜ (n +ℕ k) → Type k

-- -- --   Oₑ : ℕ → 𝓤 ⁺ ̇  
-- -- --   Oₑ k = List (Σ (_≤ℕ k)) → (o : O) → Vl o → Term k {!!}

-- -- --   -- _→ₜ_ : ∀{k} → Oₜ k → ? 


-- -- --   -- values are well typed.

-- -- --   module _ (Oₑ : ∀ {k} → TOₜ k) where
-- -- --    rule-1 : ∀{Γ k} → ∀ lsec vl → 𝓤 ̇
-- -- --    rule-1 {Γ} {k} lsec vl = [ x ∈ Γ ] k ⊢ {!!} -- Oₑ lsec vl


-- -- -- -- --   f : 𝓤 ̇
-- -- -- -- --   f = {!!}

   


-- -- -- -- -- module Context {𝓤} (Secret : 𝓤 ̇) where

-- -- -- -- --   Context : 𝓤 ⁺ ̇
-- -- -- -- --   Context = List (𝓤 ̇)

-- -- -- -- --   data diff-member : ∀ {ctx : Context} → member Secret ctx → member Secret ctx → 𝓤 ⁺ ̇  where
-- -- -- -- --     head-tail : {ctx : Context} → ∀{b : member Secret ctx} → diff-member in-head (in-tail b)
-- -- -- -- --     tail-head : {ctx : Context} → ∀{b : member Secret ctx} → diff-member (in-tail b) in-head
-- -- -- -- --     tail-tail : ∀{X} → {ctx : Context} → ∀{a b : member Secret ctx} → diff-member {ctx = X ∷ ctx} (in-tail a) (in-tail b)

-- -- -- -- --   -- In the context, we only store the Type, thus we need to introduce this elsewhere.
-- -- -- -- --   secrets-unique : Context → {!!}
-- -- -- -- --   secrets-unique ctx = (a b : member Secret ctx) → diff-member a b → {!!}

  
-- -- -- -- -- -- data _⊢_ : Context → Term
