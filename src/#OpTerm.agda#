{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Data.Nat
import Cubical.Data.Equality as E
open import Cubical.HITs.PropositionalTruncation

module OpTerm  where

private
  variable
    n : ℕ
    ℓ ℓ' ℓ'' : Level
    C D : Type ℓ
    E W : Type ℓ → Type ℓ'
    A B : Type ℓ'

_ᵖ_ : (C : Type ℓ) → ∀ ℓ' → Type (ℓ-max ℓ (ℓ-suc ℓ'))
C ᵖ ℓ' = C → Type ℓ'

[_] : {C : Type ℓ} → C ᵖ ℓ' → Type (ℓ-max ℓ ℓ')
[_] P = ∀ x → P x

OpTerm : {A : Type ℓ'} → {C : Type ℓ} → (f : A → C) → C ᵖ ℓ-max ℓ' ℓ
OpTerm f = λ x → ∥ E.fiber f x ∥₁

eqOpTExt : {A B : Type ℓ'} → {C : Type ℓ} → {f : A → C} → {g : B → C} → (∀ x → OpTerm f x → OpTerm g x)
           → (∀ x → OpTerm g x → OpTerm f x)
           → OpTerm f ≡ OpTerm g
eqOpTExt w q = funExt (λ x → hPropExt squash₁ squash₁ (w x) (q x))





-- _ᵈᵖ_ : (C : Type ℓ ᵖ ℓ') → ∀ ℓ'' → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') (ℓ-suc ℓ''))
-- _ᵈᵖ_ {ℓ = ℓ} C ℓ'' = (v : Σ (Type ℓ) λ E → E) → C (fst v) → Type ℓ'' 


-- OpTerm : {A : Type ℓ'} → {C : Type ℓ} → (f : A → C) → C ᵖ ℓ-max ℓ' ℓ
-- OpTerm f = λ x → ∥ E.fiber f x ∥₁

-- OpTerm' : {A : Type ℓ'} → {C : A → Type ℓ} → (f : (x : A) → C x) → Σ (Type ℓ) (λ E → E) ᵖ ℓ-max ℓ' (ℓ-suc ℓ)
-- OpTerm' {A = A} {C} f (E , e) = Σ (E.fiber C E) (λ x → ∥ E.transport (λ v → v) (snd x) (f (fst x)) E.≡ e ∥₁ )

-- OpTerm'' : {A : Type ℓ'} → {C : A → Type ℓ} → (f : (x : A) → C x) → Σ (Type ℓ ᵖ ℓ-max ℓ' (ℓ-suc ℓ)) λ C → C ᵈᵖ ℓ
-- fst (OpTerm'' {A = A} {C} f) = λ E → E.fiber C E
-- snd (OpTerm'' {A = A} {C} f) (.(C a) , e) (a , E.refl) = ∥ f a ≡ e ∥₁

-- -- (.(C a) , e) (a , E.refl) = ? , ∥ f a ≡ e ∥₁

-- eqOpTExt : {A B : Type ℓ'} → {C : Type ℓ} → {f : A → C} → {g : B → C} → (∀ x → OpTerm f x → OpTerm g x) → (∀ x → OpTerm g x → OpTerm f x)
--            → OpTerm f ≡ OpTerm g
-- eqOpTExt w q = funExt (λ x → hPropExt squash₁ squash₁ (w x) (q x))

-- eqOpTExt' : {A B : Type ℓ'} → {Ca : A → Type ℓ} → {Cb : B → Type ℓ} → {f : (a : A) → Ca a} → {g : (b : B) → Cb b} → (∀ E → E.fiber Ca E ≡ E.fiber Cb E ) → {!!} → {!!} → {!!} -- (∀ x → OpTerm' f x → OpTerm' g x) → (∀ x → OpTerm' g x → OpTerm' f x)
--             → OpTerm'' f ≡ OpTerm'' g
-- eqOpTExt' w q = {!!} -- funExt (λ x → hPropExt squash₁ squash₁ (w x) (q x))



-- -- pointwise
-- _⇒_ : C ᵖ ℓ → C ᵖ ℓ → C ᵖ ℓ
-- _⇒_ P W x = P x → W x


-- -- pullback
-- ⇐ : (f : A → C) → C ᵖ ℓ' → A ᵖ ℓ'
-- ⇐ f cᵖ x = cᵖ (f x)


-- -- [_] : {C : Type ℓ} → C ᵖ ℓ' → Type (ℓ-max ℓ ℓ')
-- -- [_] P = ∀ x → P x

-- -- ⟦_⟧ : {C D : Type ℓ} → C ᵖ ℓ' → Type (ℓ-max ℓ ℓ')
-- -- ⟦_⟧ {D = D} P = ∀ x → P x → D

-- -- -- df : {C : Type ℓ} → (P : C ᵖ ℓ') → [ P ] ᵖ {!!}
-- -- -- df P = {!!}

-- -- OpTerm : {A : Type ℓ'} → {C : Type ℓ} → (f : A → C) → C ᵖ ℓ-max ℓ' ℓ
-- -- OpTerm f = λ x → ∥ fiber f x ∥₁

-- -- e : {A : Type ℓ'} → {C : Type ℓ} → (f : A → C ᵖ ℓ) → (C ᵖ ℓ) ᵖ ℓ-max ℓ' (ℓ-suc ℓ)
-- -- e f = OpTerm f

-- -- w : {C D : Type ℓ} → (C ᵖ ℓ') ᵖ {!!} → Type {!!} ᵖ {!!}
-- -- w cpp = rr {!!} cpp

-- -- -- OpTerm` : {A : Type ℓ'} → {C : A → Type ℓ} → (f : (x : A) → C x) → C ᵖ ℓ-max ℓ' ℓ
-- -- -- OpTerm` f = λ x → ∥ fiber f x ∥₁


-- -- -- {-
-- -- --         f           OpTerm f 
-- -- --   A ----------> C ----------> Type    (OpTerm f) (f x) exists, is true.
-- -- --                 |
-- -- --                 | e
-- -- --                 |
-- -- --                \/      ?
-- -- --                 D -----------> Type

-- -- -- -}


-- -- -- -- OpTerm` : {A : Type ℓ} → {C : Type ℓ} → (PA : (A ᵖ ℓ')) → (C ᵖ ℓ')
-- -- -- -- OpTerm` f = {!!}



-- -- -- -- eqOpTExt : {f : A → C n} → {g : B → C n} → (∀ x → OpTerm f x → OpTerm g x) → (∀ x → OpTerm g x → OpTerm f x)
-- -- -- --            → OpTerm f ≡ OpTerm g
-- -- -- -- eqOpTExt w q = funExt (λ x → hPropExt squash₁ squash₁ (w x) (q x))


-- -- Directed Equality
-- [_]_⟨_ : ∀{A B : Type ℓ} → (e : A → B) {C : Type ℓ'} → (f : (x : A) → C) → (g : (x : B) → C) → Type (ℓ-max ℓ ℓ')
-- [_]_⟨_ {_} {_} {A} {B} e {C} f g = ∀ a → f a E.≡ g (e a)

-- ≅ : ∀{A B : Type ℓ} → (e→ : A → B) (←e : B → A) {C : Type ℓ'} → (f : (x : A) → C) → (g : (x : B) → C) → Type (ℓ-max ℓ ℓ')
-- ≅ e→ ←e f g = Σ ([ e→ ] f ⟨ g) λ _ → [ ←e ] g ⟨ f

-- [_]_⟨ᵈ_ : ∀{A B : Type ℓ} → (e : A → B) {D : B → Type ℓ'}
--      → (f : (x : A) → D (e x)) → (g : (x : B) → D x) → Type (ℓ-max ℓ ℓ')
-- [_]_⟨ᵈ_ {_} {_} {A} {B} e {D} f g = ∀ a → f a E.≡ g (e a)

-- [_]_⟨ᵈ'_ : ∀{A B : Type ℓ} → (e : A → B) {C : A → Type ℓ'} {D : B → Type ℓ'} → (∀ a → D (e a) ≡ C a)
--      → (f : (x : A) → C x) → (g : (x : B) → D x) → Type (ℓ-max ℓ ℓ')
-- [_]_⟨ᵈ'_ {_} {_} {A} {B} e {C} {D} eq f g = f E.≡ subst (λ a → a) (eq _) ∘ g ∘ e

-- ≅ᵈ : ∀{A B : Type ℓ} → (e→ : A → B) (←e : B → A) → retract ←e e→ → {D : B → Type ℓ'}
--      → (f : (x : A) → D (e→ x)) → (g : (x : B) → D x) → Type (ℓ-max ℓ ℓ')
-- ≅ᵈ {_} {_} {A} {B} e→ ←e rt {D} f g = Σ (∀ a → f a E.≡ g (e→ a)) λ _ → (b : B) → subst D (rt b) (f (←e b)) E.≡ g b


-- l2 : ∀{A B : Type ℓ} → (e→ : A → B) {C : A → Type ℓ'} {D : B → Type ℓ'} → (a : A) → C a E.≡ D (e→ a)
--      → (f : (x : A) → C x) → (g : (x : B) → D x) → Type {!!}
-- l2 e→ a eq f g = f a E.≡ E.transport (λ v → v) (E.sym eq) (g (e→ a)) 

-- l1 : ∀{A B : Type ℓ} → (e→ : A → B) (←e : B → A) {C : A → Type ℓ'} {D : B → Type ℓ'} → (eqT : ≅ e→ ←e C D)
--      → (f : (x : A) → C x) → (g : (x : B) → D x) → Type {!!}
-- l1 e→ ←e (fs , sn) f g = ∀ a → {!!}

-- -- ≅ᵈ : ∀{A B : Type ℓ} → (e→ : A → B) (←e : B → A) {C : A → Type ℓ'} {D : B → Type ℓ'}
-- --      → (f : (x : A) → C x) → (g : (x : B) → D x) → Type {!!}
-- -- ≅ᵈ {A} {B} e→ ←e {C} {D} f g = Σ (≅ e→ ←e C D) λ eqT → l1 e→ ←e eqT f g 
