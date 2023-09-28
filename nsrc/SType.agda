{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.List
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

module SType  (fe : funext 𝓤 𝓤) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇ ) where

open import BSet fe pt Msg

open BSet

module structure-statements (E : 𝓤 ⁺ ̇) where

 T⃗ : 𝓤 ⁺ ̇ 
 T⃗ = BSet  → E

 T⃖ : 𝓤 ⁺ ̇
 T⃖ = BSet  → E

 T& : 𝓤 ⁺ ̇
 T& = E → E → E

 T∣ : 𝓤 ⁺ ̇
 T∣ = E → E → E

  
module _ (E : 𝓤 ⁺ ̇) where
 open structure-statements E

 structure : (𝓤 ⁺) ⊔ (𝓤 ⁺) ̇
 structure = T⃗ × T⃖ × T& × T∣


module structure-names {E : 𝓤 ⁺ ̇ } (str : structure E) where
 open structure-statements E

 _⃗ : T⃗
 _⃗ = pr₁ str
  
 _⃖ : T⃖
 _⃖ = pr₁ (pr₂ str)

 _&_ : T&
 _&_ = pr₁ (pr₂ (pr₂ str))

 _∣_ : T∣
 _∣_ = pr₂ (pr₂ (pr₂ str))


module axiom-statements {E : 𝓤 ⁺ ̇ } (str : structure E) where
 open structure-statements E
 open structure-names str

 T&-assoc : (𝓤 ⁺)̇
 T&-assoc = (a b c : E) → a & (b ∣ c) ＝ (a & b) ∣ (a & c)

 T&-comm : (𝓤 ⁺)̇
 T&-comm = (a b : E) → a & b ＝ b & a
  
 T∣-comm : (𝓤 ⁺)̇
 T∣-comm = (a b : E) → a ∣ b ＝ b ∣ a

 T∣-idem : (𝓤 ⁺)̇
 T∣-idem = (a : E) → a ∣ a ＝ a

 record Telim {&-assoc : T&-assoc} {&-comm : T&-comm} {∣-comm : T∣-comm} {∣-idem : T∣-idem}
  : 𝓤 ⁺ ̇  where
  field
   f : {C : E → 𝓤 ̇}
     → (c→ : ∀ A → C (A ⃗))
     → (c← : ∀ A → C (A ⃖))
     → (_c&_ : (a : Σ C) → (b : Σ C) → C (pr₁ a & pr₁ b))
     → (_c∣_ : (a : Σ C) → (b : Σ C) → C (pr₁ a ∣ pr₁ b))
     → (c&-assoc : 
        (a : Σ C) → (b : Σ C) → (c : Σ C)
        → a c& (_ , b c∣ c)              ＝ transport C ((&-assoc (pr₁ a) (pr₁ b) (pr₁ c)) ⁻¹)
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
     → (x : E) → C x


module _ {E : 𝓤 ⁺ ̇ } (str : structure E) where
 open structure-statements E
 open structure-names str
 open axiom-statements str

 axioms : 𝓤 ⁺ ⊔ 𝓤 ⁺ ̇  
 axioms = T&-assoc × T&-comm × T∣-comm × T∣-idem

module axiom-names {E : 𝓤 ⁺ ̇ } {str : structure E} (ax : axioms str) where
 open axiom-statements str

 &-assoc : T&-assoc
 &-assoc = pr₁ ax
  
 &-comm : T&-comm
 &-comm = pr₁ (pr₂ ax)

 ∣-comm : T∣-comm
 ∣-comm = pr₁ (pr₂ (pr₂ ax))

 ∣-idem : T∣-idem
 ∣-idem = pr₂ (pr₂ (pr₂ ax))

module _ (E : 𝓤 ⁺ ̇ ) where

 state : 𝓤 ⁺ ̇
 state = Σ str ꞉ structure E , axioms str


record State : 𝓤 ⁺⁺ ̇  where
 field
  O : 𝓤 ⁺ ̇ 
  str : structure O
  ax : axioms str
 open structure-statements O public
 open structure-names str public
 open axiom-statements str public
 open axiom-names {str = str} ax public
 field
  elim : Telim {&-assoc} {&-comm} {∣-comm} {∣-idem}

module _ (d : State) (open State d) (Vl : O → 𝓤 ̇ ) where

 module value-structure-statements where
 
  V⃗ : 𝓤 ⁺ ̇  
  V⃗ = (mp : Msg) → ∀ A → ⦃ P : ⟨ A ⟩ mp ⦄ → Vl (A ⃗) 
 
  V⃖ : 𝓤 ⁺ ̇  
  V⃖ = ∀ A → Vl (A ⃖) 
 
  V& : 𝓤 ⁺ ̇
  V& = {X Y : O} → (x : Vl X) → (y : Vl Y) → Vl (X & Y)
 
  V∣ : 𝓤 ⁺ ̇
  V∣ = {X Y : O} → (x : Vl X) → (y : Vl Y) → Vl (X ∣ Y)

 module _ where
  open value-structure-statements
 
  value-structure : (𝓤 ⁺) ⊔ (𝓤 ⁺) ̇
  value-structure = V⃗ × V⃖ × V& × V∣
 
 
 module value-structure-names (vl : value-structure) where
  open value-structure-statements
 
  _⃗∈_ : V⃗
  _⃗∈_ = pr₁ vl
   
  ⃖_ : V⃖
  ⃖_ = pr₁ (pr₂ vl)
 
  _＆_ : V&
  _＆_ = pr₁ (pr₂ (pr₂ vl))
 
  _∥_ : V∣
  _∥_ = pr₂ (pr₂ (pr₂ vl))

 module value-axiom-statements (vl : value-structure) where
  open value-structure-statements
  open value-structure-names vl

  T∥-idem : (𝓤 ⁺)̇
  T∥-idem = {A : O} → (a : Vl A) → (eq : A ＝ (A ∣ A)) → a ∥ a ＝ transport Vl eq a

 -- these properties are derivable from the above.
  T＆-assoc : (𝓤 ⁺)̇
  T＆-assoc = {A B C : O} → (a : Vl A) → (b : Vl B) → (c : Vl C) → (eq : ((A & B) ∣ (A & C)) ＝ (A & (B ∣ C))) → a ＆ (b ∥ c) ＝ transport Vl eq ((a ＆ b) ∥ (a ＆ c))
 
  T＆-comm : (𝓤 ⁺)̇
  T＆-comm = {A B : O} → (a : Vl A) → (b : Vl B) → (eq : (B & A) ＝ (A & B)) → a ＆ b ＝ transport Vl eq (b ＆ a)
   
  T∥-comm : (𝓤 ⁺)̇
  T∥-comm = {A B : O} → (a : Vl A) → (b : Vl B) → (eq : (B ∣ A) ＝ (A ∣ B)) → a ∥ b ＝ transport Vl eq (b ∥ a)

  record TVelim {＆-assoc : T＆-assoc} {＆-comm : T＆-comm} {∥-comm : T∥-comm} {∥-idem : T∥-idem}
   : 𝓤 ⁺ ̇  where
   field
    f : {C : (o : O) → Vl o → 𝓤 ̇}
        → (c→ : ∀ msg → ∀ A → ⦃ P : ⟨ A ⟩ msg ⦄ → C _ (msg ⃗∈ A))
        → (c← : ∀ A → C _ ( ⃖ A))
        → (_c&_ : ∀{oa ob} → (a : Σ (C oa)) → (b : Σ (C ob)) → let va = pr₁ a
                                                                   vb = pr₁ b
                                                                   in C _ (va ＆ vb))
        → (_c∣_ : ∀{oa ob} → (a : Σ (C oa)) → (b : Σ (C ob)) → C _ (pr₁ a ∥ pr₁ b))

----------------------------
        → (c∥-idem : ∀{oa} → (a : Σ (C oa)) →
          pr₂ a
        ＝
          transport
           (λ o → (a : Σ (C oa)) → let va = pr₁ a in (oeq : o ＝ oa) → (vl : Vl o) → vl ＝ transport Vl (oeq ⁻¹) va → C _ vl)
           (∣-idem oa)
           (λ a oeq vl veq → let va = pr₁ a
                             in transport (C _) (∥-idem va (oeq ⁻¹) ∙ veq ⁻¹) (a c∣ a)) a refl (pr₁ a) refl)
-------------------------
        → (c&-assoc : ∀{oa ob oc} →
           (a : Σ (C oa)) → (b : Σ (C ob)) → (c : Σ (C oc))
           →   a c& (_ , b c∣ c)
             ＝
               (transport (λ o → (a : Σ (C oa)) → let va = pr₁ a in (b : Σ (C ob)) → let vb = pr₁ b in (c : Σ (C oc)) → let vc = pr₁ c in (oeq : o ＝ (oa & (ob ∣ oc))) → (vl : Vl o) → vl ＝ transport Vl (oeq ⁻¹) (va ＆ (vb ∥ vc)) → C _ vl)
                 (&-assoc oa ob oc ⁻¹)
                 λ a b c oeq vl veq → let va = pr₁ a
                                          vb = pr₁ b
                                          vc = pr₁ c
                                      in transport (C _) ((ap (transport Vl (oeq ⁻¹)) (＆-assoc va vb vc oeq) ∙ forth-and-back-transport oeq) ⁻¹ ∙ veq ⁻¹) ((_ , (a c& b)) c∣ (_ , a c& c))) a b c refl (pr₁ a ＆ (pr₁ b ∥ pr₁ c) ) refl)
---------------------------
        → (c∣-comm : ∀{oa ob} → (a : Σ (C oa)) → (b : Σ (C ob)) →
          a c∣ b
        ＝
          transport
           (λ o → (a : Σ (C oa)) → (b : Σ (C ob)) → let va = pr₁ a
                                                        vb = pr₁ b
                                                    in (oeq : o ＝ oa ∣ ob) → (vl : Vl o) → vl ＝ transport Vl (oeq ⁻¹) (va ∥ vb) → C _ vl)
           (∣-comm ob oa)
           (λ a b oeq vl veq → transport (C _) (∥-comm (pr₁ b) (pr₁ a) (oeq ⁻¹) ∙ veq ⁻¹) (b c∣ a))
           a b refl (pr₁ a ∥ pr₁ b) refl)
------------------------------
        → (c&-comm : ∀{oa ob} → (a : Σ (C oa)) → (b : Σ (C ob)) →
          a c& b
        ＝
          transport
           (λ o → (a : Σ (C oa)) → (b : Σ (C ob)) → let va = pr₁ a
                                                        vb = pr₁ b
                                                    in (oeq : o ＝ oa & ob) → (vl : Vl o) → vl ＝ transport Vl (oeq ⁻¹) (va ＆ vb) → C _ vl)
           (&-comm ob oa)
           (λ a b oeq vl veq → transport (C _) (＆-comm (pr₁ b) (pr₁ a) (oeq ⁻¹) ∙ veq ⁻¹) (b c& a))
           a b refl (pr₁ a ＆ pr₁ b) refl)
      → {o : O} → (v : Vl o) → C _ v



 module _ (vl : value-structure) where
  open value-structure-statements
  open value-structure-names vl 
  open value-axiom-statements vl

  value-axioms : 𝓤 ⁺ ⊔ 𝓤 ⁺ ̇  
  value-axioms = T＆-assoc × T＆-comm × T∥-comm × T∥-idem

 module value-axiom-names {vstr : value-structure} (vax : value-axioms vstr) where
  open value-axiom-statements vstr

  ＆-assoc : T＆-assoc
  ＆-assoc = pr₁ vax

  ＆-comm : T＆-comm
  ＆-comm = pr₁ (pr₂ vax)

  ∥-comm : T∥-comm
  ∥-comm = pr₁ (pr₂ (pr₂ vax))

  ∥-idem : T∥-idem
  ∥-idem =  pr₂ (pr₂ (pr₂ vax))

 vstate : 𝓤 ⁺ ̇
 vstate = Σ vstr ꞉ value-structure , value-axioms vstr

module _ (d : State) (open State d) where
 record VState : 𝓤 ⁺ ̇  where
  field
   Vl : O → 𝓤 ̇
   vstr : value-structure d Vl
   vax : value-axioms d Vl vstr

  open value-structure-statements public
  open value-structure-names d Vl vstr public
  open value-axiom-statements d Vl vstr public
  open value-axiom-names d Vl {vstr = vstr} vax public
  field
   elim : TVelim {＆-assoc} {＆-comm} {∥-comm} {∥-idem}


semilist-structure : ∀{𝓤} → 𝓤 ̇  → 𝓤 ̇  → 𝓤 ̇
semilist-structure X A = (X → X → X) × (A → X)


semilist-axioms : ∀{𝓤} → (X : 𝓤 ̇ ) → (A : 𝓤 ̇) → semilist-structure X A → 𝓤 ̇
semilist-axioms X A str@(_·_ , _) = -- is-set X
                                 commutative     _·_
                               × associative     _·_

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
  *-assoc = pr₂ ax

record Semilist {𝓤} (X : 𝓤 ̇ ) (A : 𝓤 ̇) : 𝓤 ⁺ ̇  where
 field
  mstr : semilist-structure X A
  mmax : semilist-axioms _ _ mstr

 open semilist-structure-names mstr public
 open semilist-axiom-names mmax public
 field
  selim : {C : X → 𝓤 ̇}
       → (c` : (x : A) → C (` x))
       → (_c*_ : (a b : Σ C) → let xa = pr₁ a
                                   xb = pr₁ b
                               in C (xa * xb))
       → (c*-comm : (a b : Σ C) → a c* b ＝ transport C (*-comm _ _) (b c* a))
       → (c*-assoc : (a b c : Σ C) → a c* (_ , b c* c) ＝ transport C (*-assoc _ _ _) ((_ , a c* b) c* c))
       → (x : X) → C x



module Context (Secret : 𝓤 ̇) where

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

module _ where

 SFun : ∀{C : 𝓤 ⁺⁺ ̇} → 𝓤 ⁺⁺ ̇ 
 SFun {C} = 𝟚 × (Σ A ꞉ BSet , ((mp : Msg) → { ⟨ A ⟩ mp } → C))
   

 Sheaf : ∀ X C → (𝓤 ⁺⁺ ⁺) ̇
 Sheaf X C = Semilist X (SFun {C})

module _ (Secret : 𝓤 ̇) (d : State) (open State d) (O→ : O → 𝓤 ⁺⁺ ̇ ) where

 open Context Secret


 module function-structure-statements where

  F⃗ : 𝓤 ⁺⁺ ̇
  F⃗ = (A : BSet) → ((mp : Msg) → { ⟨ A ⟩ mp } → OpenΣ (O + Σ O→)) → O→ (A ⃗)
 
  F⃖ : 𝓤 ⁺⁺ ̇
  F⃖ = (A : BSet) → ((mp : Msg) → { ⟨ A ⟩ mp } → OpenΣ (O + Σ O→)) → O→ (A ⃖)

  F& : 𝓤 ⁺⁺ ̇ 
  F& = ∀{A B} → (a : O→ A) → (b : O→ B) → O→ (A & B)
   
  F∣ : 𝓤 ⁺⁺ ̇ 
  F∣ = ∀{A B} → (a : O→ A) → (b : O→ B) → O→ (A ∣ B)

 module _ where
  open function-structure-statements
 
  function-structure : 𝓤 ⁺⁺ ̇
  function-structure = F⃗ × F⃖ × F& × F∣
 
 
 module function-structure-names (str : function-structure) where
  open function-structure-statements
 
  _ᶠ⃗ : F⃗
  _ᶠ⃗ = pr₁ str

  _ᶠ⃖ : F⃖
  _ᶠ⃖ = pr₁ (pr₂ str)

  _&ᶠ_ : F&
  _&ᶠ_ = pr₁ (pr₂ (pr₂ str))

  _∣ᶠ_ : F∣
  _∣ᶠ_ = pr₂ (pr₂ (pr₂ str))


 record fstate : 𝓤 ⁺⁺ ̇  where
  field
   fstr : function-structure

  open function-structure-statements public
  open function-structure-names fstr public


 module _ (fst : fstate) {X} (fmlt : Sheaf X (OpenΣ (O + Σ O→))) where
  open Semilist fmlt

  F⃗-to-Sheaf : (A : BSet) → ((mp : Msg) → { ⟨ A ⟩ mp } → OpenΣ (O + Σ O→)) → X
  F⃗-to-Sheaf A x = ` (⇒ , (A , x ))

  F⃖-to-Sheaf : (A : BSet) → ((mp : Msg) → { ⟨ A ⟩ mp } → OpenΣ (O + Σ O→)) → X
  F⃖-to-Sheaf A x = ` (⇐ , (A , x ))

  F&-to-Sheaf : ∀{A B} → (a : O→ A × X) → (b : O→ B × X) → X
  F&-to-Sheaf (a , ax) (b , bx) =
   (selim
    (λ { (d , (BS , f)) → {!!}})
    {!!}
    {!!}
    {!!}
     bx)
     *
    {!!}

--   g : ∀ A → O→ A → X
--   g = {!!}

-- -- module _ (d : State) (v : VState d) (Secret : 𝓤 ̇) where
-- --  open Context Secret
-- --  open State d
-- --  open VState v

-- --  module _ (Type : ℕ → 𝓤 ̇) (Term : (k : ℕ) → Type k → 𝓤 ̇ ) (WQ : (x : Ctx) → (k : ℕ) → (Vars {x} → Σ (Term k)) → 𝓤 ̇) where

-- --   W : (x : Ctx) → (k : ℕ) → (Vars {x} → Σ (Term k)) → 𝓤 ̇
-- --   W x k B = WQ x k B
  
-- --   syntax W Γ k (λ vars → B) = [ vars ∈ Γ ] k ⊢ B

-- --   TOₜ : ℕ → 𝓤 ⁺ ̇   
-- --   TOₜ k = List (Σ (_≤ℕ k)) → O → Type k

-- --   TOₜ→Oₜ : ℕ → 𝓤 ⁺ ̇
-- --   TOₜ→Oₜ k = TOₜ k → (n : ℕ) → TOₜ (n +ℕ k) → Type k

-- --   Oₑ : ℕ → 𝓤 ⁺ ̇  
-- --   Oₑ k = List (Σ (_≤ℕ k)) → (o : O) → Vl o → Term k {!!}

-- --   -- _→ₜ_ : ∀{k} → Oₜ k → ? 


-- --   -- values are well typed.

-- --   module _ (Oₑ : ∀ {k} → TOₜ k) where
-- --    rule-1 : ∀{Γ k} → ∀ lsec vl → 𝓤 ̇
-- --    rule-1 {Γ} {k} lsec vl = [ x ∈ Γ ] k ⊢ {!!} -- Oₑ lsec vl


-- -- -- --   f : 𝓤 ̇
-- -- -- --   f = {!!}

   


-- -- -- -- module Context {𝓤} (Secret : 𝓤 ̇) where

-- -- -- --   Context : 𝓤 ⁺ ̇
-- -- -- --   Context = List (𝓤 ̇)

-- -- -- --   data diff-member : ∀ {ctx : Context} → member Secret ctx → member Secret ctx → 𝓤 ⁺ ̇  where
-- -- -- --     head-tail : {ctx : Context} → ∀{b : member Secret ctx} → diff-member in-head (in-tail b)
-- -- -- --     tail-head : {ctx : Context} → ∀{b : member Secret ctx} → diff-member (in-tail b) in-head
-- -- -- --     tail-tail : ∀{X} → {ctx : Context} → ∀{a b : member Secret ctx} → diff-member {ctx = X ∷ ctx} (in-tail a) (in-tail b)

-- -- -- --   -- In the context, we only store the Type, thus we need to introduce this elsewhere.
-- -- -- --   secrets-unique : Context → {!!}
-- -- -- --   secrets-unique ctx = (a b : member Secret ctx) → diff-member a b → {!!}

  
-- -- -- -- -- data _⊢_ : Context → Term
