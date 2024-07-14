{-# OPTIONS --safe --without-K --exact-split --guardedness #-}

open import MLTT.Spartan hiding (rec)
open import MLTT.List
open import MLTT.Maybe
open import MLTT.Bool as B
open import MLTT.Vector
open import UF.Subsingletons
open import Naturals.Order
open import UF.FunExt
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Notation.General
open import UF.Sets
open import UF.Sets-Properties
open import UF.Base
open import UF.Embeddings
open import MLTT.Two renaming (₀ to 𝕞 ; ₁ to 𝕒)
import UF.ImageAndSurjection
open import Quotient.Type

open import Common
open import Free
import Sheaf

module OpTerm (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓥 ̇) where

open PropositionalTruncation pt
open UF.ImageAndSurjection pt

open Sheaf fe pt Msg

module Context {𝓥 𝓦} (Secret : 𝓥 ̇) where

-- TODO Secrets are unique ??? Hey, we dont need this because we perform the construction ??

 data Ctx : (n : ℕ) → 𝓥 ⁺ ̇  where
  []ᶜ : Ctx zero
  _∶ᶜ_ : ∀{n} → (X : 𝓥 ̇ ) → (X → Ctx n) → Ctx (succ n)

 _++ᶜ_ : ∀{a b} → Ctx a → Ctx b → Ctx (b +ℕ a)
 []ᶜ ++ᶜ cb = cb
 (X ∶ᶜ xs) ++ᶜ cb = X ∶ᶜ λ x → xs x ++ᶜ cb

 λCtx : ℕ → ℕ → 𝓥 ⁺ ̇
 λCtx k n = Vector Secret k → Ctx n


 Vars : ∀{k n} → Vector Secret k → λCtx k n → 𝓥 ̇
 Vars x v = l1 (v x) where
  l1 : ∀{k} → Ctx k → Set 𝓥
  l1 []ᶜ = 𝟙
  l1 (X ∶ᶜ xs) = Σ x ꞉ _ , l1 (xs x)



 Input : Σ k ꞉ ℕ , Σ n ꞉ ℕ , λCtx k n
      → 𝓥 ̇ 
 Input (k , _ , λctx) = Σ secrets ꞉ Vector Secret k , Vars secrets λctx

 Open : (C : 𝓦 ̇ ) → Σ k ꞉ ℕ , Σ n ꞉ ℕ , λCtx k n
      → (𝓥 ⊔ 𝓦)̇ 
 Open  C e = Input e → C

 OpenΣ : (C : 𝓦 ̇) → (𝓥 ⁺ ⊔ 𝓦) ̇
 OpenΣ C = Σ (Open C)

 _⊂_ : ∀{C} → (op1 op2 : OpenΣ C) → 𝓥 ⊔ 𝓦 ̇
 (i1 , o1) ⊂ (i2 , o2) = (x1 : Input i1) → (o1 x1) ∈image o2

 _⊃_ : ∀{C} → (op1 op2 : OpenΣ C) → 𝓥 ⊔ 𝓦 ̇
 op1 ⊃ op2 = op2 ⊂ op1

 ⊂-trans : ∀{C} → {op1 op2 op3 : OpenΣ C} → op1 ⊂ op2 → op2 ⊂ op3 → op1 ⊂ op3
 ⊂-trans ⊂1 ⊂2 x = ∥∥-induction (λ _ → being-in-the-image-is-prop _ _)
  (λ (x2 , eq2) → ∥∥-induction (λ _ → being-in-the-image-is-prop _ _)
  (λ (x3 , eq3) → ∣ x3 , (eq3 ∙ eq2) ∣) (⊂2 x2)) (⊂1 x)

 _~_ : ∀{C} → (op1 op2 : OpenΣ C) → 𝓥 ⊔ 𝓦 ̇
 op1 ~ op2 = op1 ⊂ op2 × (op2 ⊂ op1)

 ~eqv :  ∀{C} → EqRel (OpenΣ C)
 pr₁ ~eqv = _~_
 pr₁ (pr₂ ~eqv) = λ x y → ×-is-prop (Π-is-prop fe (λ _ → being-in-the-image-is-prop _ _)) (Π-is-prop fe (λ _ → being-in-the-image-is-prop _ _))
 pr₁ (pr₁ (pr₂ (pr₂ ~eqv)) op) x1 = ∣ x1 , refl ∣ 
 pr₂ (pr₁ (pr₂ (pr₂ ~eqv)) op) x1 = ∣ x1 , refl ∣ 
 pr₁ (pr₂ (pr₂ (pr₂ ~eqv))) x y (a , b) = b , a
 pr₂ (pr₂ (pr₂ (pr₂ ~eqv))) x y z ~1 ~2 = (⊂-trans (pr₁ ~1) (pr₁ ~2)) , (⊂-trans (pr₂ ~2) (pr₂ ~1))



-- F-coalgebra with the use of Sheaf g     F X → 𝟙 ⊎ A × X

module _ {𝓤} (Secret : 𝓥 ̇ ) (o : OSet 𝓤) (qt : general-set-quotients-exist id) where

 private
  module O = OSet o
  module Qt = general-set-quotients-exist qt

 open fO→B o

 module _ where

  open Context {𝓦 = 𝓤 ⊔ 𝓥 ⁺} Secret
  record W : 𝓤 ⊔ 𝓥 ⁺ ̇  where
   coinductive
   field
    e : O.E
    sh : (msg : 𝟚 × Msg) → fO→B msg e ＝ true ̂  → OpenΣ W
    
  open W
 
  record _~W_ (w1 w2 : W) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
   field
    _~e_  : e w1 ＝ e w2
    _~sh_ : (msg : 𝟚 × Msg) → (cnd : fO→B msg (e w1) ＝ true ̂ )
            → sh w1 msg cnd ~ sh w2 msg (ap (fO→B msg) (_~e_ ⁻¹) ∙ cnd )
 

_ᵖ : (C : 𝓤 ̇ ) → 𝓤 ⁺ ̇
_ᵖ {𝓤} C = Σ A ꞉ (C → 𝓤 ̇ ) , is-prop-valued-family A

OpTerm : {A : 𝓤 ̇ } → {C : 𝓤 ̇ } → (f : A → C) → C ᵖ
OpTerm f = _∈image f , λ x → being-in-the-image-is-prop x f

module eedf {𝓤} (d : icommonoid {𝓤 = 𝓤}) where
 private
  module D = icommonoid d
  
 _-|-_ : D.E ᵖ → D.E ᵖ → D.E ᵖ
 a -|- b = OpTerm e where
  e : Σ (pr₁ a) × Σ (pr₁ b) → _
  e ((x , _) , (y , _)) = x D.* y

 pred-icommonoid : icommonoid
 icommonoid.E pred-icommonoid = D.E ᵖ
 icommonoid.str pred-icommonoid = _-|-_ , (λ x → 𝟘) , λ x → 𝟘-is-prop
 pr₁ (pr₁ (icommonoid.ax pred-icommonoid)) a b c = {!!}
 pr₂ (pr₁ (icommonoid.ax pred-icommonoid)) = {!!}
 pr₁ (pr₂ (icommonoid.ax pred-icommonoid)) = {!!}
 pr₂ (pr₂ (icommonoid.ax pred-icommonoid)) a
  = to-subtype-＝
   (λ x a b → {!!})
   (dfunext fe λ x → {!!})


-- [_] : {C : Type ℓ} → C ᵖ ℓ' → Type (ℓ-max ℓ ℓ')
-- [_] P = ∀ x → P x

-- OpTerm : {A : Type ℓ'} → {C : Type ℓ} → (f : A → C) → C ᵖ ℓ-max ℓ' ℓ
-- OpTerm f = λ y → ∥ E.fiber f y ∥₁

-- eqOpTExt : {A B : Type ℓ'} → {C : Type ℓ} → {f : A → C} → {g : B → C} → (∀ x → OpTerm f x → OpTerm g x)
--            → (∀ x → OpTerm g x → OpTerm f x)
--            → OpTerm f ≡ OpTerm g
-- eqOpTExt w q = funExt (λ x → hPropExt squash₁ squash₁ (w x) (q x))





-- -- _ᵈᵖ_ : (C : Type ℓ ᵖ ℓ') → ∀ ℓ'' → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') (ℓ-suc ℓ''))
-- -- _ᵈᵖ_ {ℓ = ℓ} C ℓ'' = (v : Σ (Type ℓ) λ E → E) → C (fst v) → Type ℓ'' 


-- -- OpTerm : {A : Type ℓ'} → {C : Type ℓ} → (f : A → C) → C ᵖ ℓ-max ℓ' ℓ
-- -- OpTerm f = λ x → ∥ E.fiber f x ∥₁

-- -- OpTerm' : {A : Type ℓ'} → {C : A → Type ℓ} → (f : (x : A) → C x) → Σ (Type ℓ) (λ E → E) ᵖ ℓ-max ℓ' (ℓ-suc ℓ)
-- -- OpTerm' {A = A} {C} f (E , e) = Σ (E.fiber C E) (λ x → ∥ E.transport (λ v → v) (snd x) (f (fst x)) E.≡ e ∥₁ )

-- -- OpTerm'' : {A : Type ℓ'} → {C : A → Type ℓ} → (f : (x : A) → C x) → Σ (Type ℓ ᵖ ℓ-max ℓ' (ℓ-suc ℓ)) λ C → C ᵈᵖ ℓ
-- -- fst (OpTerm'' {A = A} {C} f) = λ E → E.fiber C E
-- -- snd (OpTerm'' {A = A} {C} f) (.(C a) , e) (a , E.refl) = ∥ f a ≡ e ∥₁

-- -- -- (.(C a) , e) (a , E.refl) = ? , ∥ f a ≡ e ∥₁

-- -- eqOpTExt : {A B : Type ℓ'} → {C : Type ℓ} → {f : A → C} → {g : B → C} → (∀ x → OpTerm f x → OpTerm g x) → (∀ x → OpTerm g x → OpTerm f x)
-- --            → OpTerm f ≡ OpTerm g
-- -- eqOpTExt w q = funExt (λ x → hPropExt squash₁ squash₁ (w x) (q x))

-- -- eqOpTExt' : {A B : Type ℓ'} → {Ca : A → Type ℓ} → {Cb : B → Type ℓ} → {f : (a : A) → Ca a} → {g : (b : B) → Cb b} → (∀ E → E.fiber Ca E ≡ E.fiber Cb E ) → {!!} → {!!} → {!!} -- (∀ x → OpTerm' f x → OpTerm' g x) → (∀ x → OpTerm' g x → OpTerm' f x)
-- --             → OpTerm'' f ≡ OpTerm'' g
-- -- eqOpTExt' w q = {!!} -- funExt (λ x → hPropExt squash₁ squash₁ (w x) (q x))



-- -- -- pointwise
-- -- _⇒_ : C ᵖ ℓ → C ᵖ ℓ → C ᵖ ℓ
-- -- _⇒_ P W x = P x → W x


-- -- -- pullback
-- -- ⇐ : (f : A → C) → C ᵖ ℓ' → A ᵖ ℓ'
-- -- ⇐ f cᵖ x = cᵖ (f x)


-- -- -- [_] : {C : Type ℓ} → C ᵖ ℓ' → Type (ℓ-max ℓ ℓ')
-- -- -- [_] P = ∀ x → P x

-- -- -- ⟦_⟧ : {C D : Type ℓ} → C ᵖ ℓ' → Type (ℓ-max ℓ ℓ')
-- -- -- ⟦_⟧ {D = D} P = ∀ x → P x → D

-- -- -- -- df : {C : Type ℓ} → (P : C ᵖ ℓ') → [ P ] ᵖ {!!}
-- -- -- -- df P = {!!}

-- -- -- OpTerm : {A : Type ℓ'} → {C : Type ℓ} → (f : A → C) → C ᵖ ℓ-max ℓ' ℓ
-- -- -- OpTerm f = λ x → ∥ fiber f x ∥₁

-- -- -- e : {A : Type ℓ'} → {C : Type ℓ} → (f : A → C ᵖ ℓ) → (C ᵖ ℓ) ᵖ ℓ-max ℓ' (ℓ-suc ℓ)
-- -- -- e f = OpTerm f

-- -- -- w : {C D : Type ℓ} → (C ᵖ ℓ') ᵖ {!!} → Type {!!} ᵖ {!!}
-- -- -- w cpp = rr {!!} cpp

-- -- -- -- OpTerm` : {A : Type ℓ'} → {C : A → Type ℓ} → (f : (x : A) → C x) → C ᵖ ℓ-max ℓ' ℓ
-- -- -- -- OpTerm` f = λ x → ∥ fiber f x ∥₁


-- -- -- -- {-
-- -- -- --         f           OpTerm f 
-- -- -- --   A ----------> C ----------> Type    (OpTerm f) (f x) exists, is true.
-- -- -- --                 |
-- -- -- --                 | e
-- -- -- --                 |
-- -- -- --                \/      ?
-- -- -- --                 D -----------> Type

-- -- -- -- -}


-- -- -- -- -- OpTerm` : {A : Type ℓ} → {C : Type ℓ} → (PA : (A ᵖ ℓ')) → (C ᵖ ℓ')
-- -- -- -- -- OpTerm` f = {!!}



-- -- -- -- -- eqOpTExt : {f : A → C n} → {g : B → C n} → (∀ x → OpTerm f x → OpTerm g x) → (∀ x → OpTerm g x → OpTerm f x)
-- -- -- -- --            → OpTerm f ≡ OpTerm g
-- -- -- -- -- eqOpTExt w q = funExt (λ x → hPropExt squash₁ squash₁ (w x) (q x))


-- -- -- Directed Equality
-- -- [_]_⟨_ : ∀{A B : Type ℓ} → (e : A → B) {C : Type ℓ'} → (f : (x : A) → C) → (g : (x : B) → C) → Type (ℓ-max ℓ ℓ')
-- -- [_]_⟨_ {_} {_} {A} {B} e {C} f g = ∀ a → f a E.≡ g (e a)

-- -- ≅ : ∀{A B : Type ℓ} → (e→ : A → B) (←e : B → A) {C : Type ℓ'} → (f : (x : A) → C) → (g : (x : B) → C) → Type (ℓ-max ℓ ℓ')
-- -- ≅ e→ ←e f g = Σ ([ e→ ] f ⟨ g) λ _ → [ ←e ] g ⟨ f

-- -- [_]_⟨ᵈ_ : ∀{A B : Type ℓ} → (e : A → B) {D : B → Type ℓ'}
-- --      → (f : (x : A) → D (e x)) → (g : (x : B) → D x) → Type (ℓ-max ℓ ℓ')
-- -- [_]_⟨ᵈ_ {_} {_} {A} {B} e {D} f g = ∀ a → f a E.≡ g (e a)

-- -- [_]_⟨ᵈ'_ : ∀{A B : Type ℓ} → (e : A → B) {C : A → Type ℓ'} {D : B → Type ℓ'} → (∀ a → D (e a) ≡ C a)
-- --      → (f : (x : A) → C x) → (g : (x : B) → D x) → Type (ℓ-max ℓ ℓ')
-- -- [_]_⟨ᵈ'_ {_} {_} {A} {B} e {C} {D} eq f g = f E.≡ subst (λ a → a) (eq _) ∘ g ∘ e

-- -- ≅ᵈ : ∀{A B : Type ℓ} → (e→ : A → B) (←e : B → A) → retract ←e e→ → {D : B → Type ℓ'}
-- --      → (f : (x : A) → D (e→ x)) → (g : (x : B) → D x) → Type (ℓ-max ℓ ℓ')
-- -- ≅ᵈ {_} {_} {A} {B} e→ ←e rt {D} f g = Σ (∀ a → f a E.≡ g (e→ a)) λ _ → (b : B) → subst D (rt b) (f (←e b)) E.≡ g b


-- -- l2 : ∀{A B : Type ℓ} → (e→ : A → B) {C : A → Type ℓ'} {D : B → Type ℓ'} → (a : A) → C a E.≡ D (e→ a)
-- --      → (f : (x : A) → C x) → (g : (x : B) → D x) → Type {!!}
-- -- l2 e→ a eq f g = f a E.≡ E.transport (λ v → v) (E.sym eq) (g (e→ a)) 

-- -- l1 : ∀{A B : Type ℓ} → (e→ : A → B) (←e : B → A) {C : A → Type ℓ'} {D : B → Type ℓ'} → (eqT : ≅ e→ ←e C D)
-- --      → (f : (x : A) → C x) → (g : (x : B) → D x) → Type {!!}
-- -- l1 e→ ←e (fs , sn) f g = ∀ a → {!!}

-- -- -- ≅ᵈ : ∀{A B : Type ℓ} → (e→ : A → B) (←e : B → A) {C : A → Type ℓ'} {D : B → Type ℓ'}
-- -- --      → (f : (x : A) → C x) → (g : (x : B) → D x) → Type {!!}
-- -- -- ≅ᵈ {A} {B} e→ ←e {C} {D} f g = Σ (≅ e→ ←e C D) λ eqT → l1 e→ ←e eqT f g 
