{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc

module BSet (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) where

open PropositionalTruncation pt

-- A property on messages
-- TODO Should the predicates have the same universe with the message ?
record BSet : 𝓤 ⁺ ̇  where
 constructor bst
 field
  ⟨_⟩ : (mp : Msg) → 𝓤 ̇ 
  -is-prop : ∀ mp → is-prop (⟨_⟩ mp)

open BSet public

BPred : 𝓤 ⁺ ̇
BPred = ((mp : Msg) → 𝓤 ̇ )

BSet' : 𝓤 ⁺ ̇
BSet' = Σ P ꞉ ((mp : Msg) → 𝓤 ̇ ) , (∀ mp → is-prop (P mp))

⟨_⟩' : BSet' → (Msg → 𝓤 ̇)
⟨ bs ⟩' = bs .pr₁

_is-prop' : (bs : BSet') → (∀ mp → is-prop (⟨ bs ⟩' mp))
bs is-prop' = bs .pr₂

_toBSet : BSet' → BSet
⟨ bs toBSet ⟩ = bs .pr₁
(bs toBSet) .-is-prop = bs .pr₂

_toBSet' : BSet → BSet'
bs toBSet' = ⟨ bs ⟩ , bs .-is-prop

-- The property holds for all messages.
⊨ : BSet → 𝓤 ̇
⊨ P = ∀ a → ⟨ P ⟩ a 

⊥B : BSet
⟨ ⊥B ⟩ mp = 𝟘
⊥B .-is-prop mp = 𝟘-is-prop

⊤B : BSet
⟨ ⊤B ⟩ mp = 𝟙
⊤B .-is-prop mp = 𝟙-is-prop

_⟶_ : BSet → BSet → BSet
⟨ P ⟶ Q ⟩ mp = ⟨ P ⟩ mp → ⟨ Q ⟩ mp
(P ⟶ Q) .-is-prop mp = Π-is-prop fe (λ _ → (Q .-is-prop) mp)


_&&'_ : BSet' → BSet' → BSet'
a &&' b  = (λ mp → ⟨ a ⟩' mp × ⟨ b ⟩' mp) , λ mp → Σ-is-prop ((a is-prop') mp) (λ _ → ((b is-prop') mp))

_&&_ : BSet → BSet → BSet
⟨ a && b ⟩ mp = ⟨ a ⟩ mp × ⟨ b ⟩  mp
((a && b) .-is-prop) mp = Σ-is-prop ((a .-is-prop) mp) (λ _ → ((b .-is-prop) mp))


_≡ᵇ_ : BSet → BSet → 𝓤 ̇
A ≡ᵇ B = ⊨ ((A ⟶ B) && (B ⟶ A))

¬ᵇ' : BSet' → BSet'
¬ᵇ' bs = (λ mp → ¬ (⟨ bs ⟩' mp)) , (λ mp → Π-is-prop fe λ _ → 𝟘-is-prop)

¬ᵇ : BSet → BSet
⟨ ¬ᵇ A ⟩ mp = ¬ (⟨ A ⟩ mp)
-is-prop (¬ᵇ A) mp = Π-is-prop fe λ _ → 𝟘-is-prop

-- I do not like this definition, because we need to prove the negation
--  update : But since we have decidability anyway, this is provable immediately
_─_ : BSet → BSet → BSet
(a ─ b) = a && (¬ᵇ b)

_|x|'_ : BSet' → BSet' → BSet'
(a |x|' b) .pr₁ = λ mp → ⟨ ¬ᵇ' (a &&' b) ⟩' mp × (⟨ a ⟩' mp + ⟨ b ⟩' mp)
(a |x|' b) .pr₂ = λ mp → Σ-is-prop
    (((¬ᵇ' (a &&' b)) is-prop') mp)
    (λ ¬pa&b → +-is-prop ((a is-prop') mp)
    ((b is-prop') mp)
    λ pa pb → ¬pa&b (pa , pb))

_|x|_ : BSet → BSet → BSet
⟨ a |x| b ⟩ mp = ⟨ ¬ᵇ (a && b) ⟩ mp × (⟨ a ⟩ mp + ⟨ b ⟩ mp)
-is-prop (a |x| b) mp
 = Σ-is-prop
    (¬ᵇ (a && b) .-is-prop mp)
    (λ ¬pa&b → +-is-prop (a .-is-prop mp)
    (b .-is-prop mp)
    λ pa pb → ¬pa&b (pa , pb))

-- I have defined it this way, so as to be a proposition.
-- Is this the best way?

_||'_ : BSet' → BSet' → BSet'
a ||' b = (λ mp → ⟨ a &&' b ⟩' mp + ⟨ ¬ᵇ' (a &&' b) ⟩' mp × (⟨ a ⟩' mp + ⟨ b ⟩' mp))
 , (λ { mp (inl x) (inl y) → ap inl (((a &&' b) is-prop') mp x y)
      ; mp (inl x) (inr y) → 𝟘-elim (pr₁ y x)
      ; mp (inr x) (inl y) → 𝟘-elim (pr₁ x y)
      ; mp (inr x) (inr y) → ap inr (((a |x|' b) is-prop') mp x y)})


_||''_ : BSet' → BSet' → BSet'
(a ||'' b) .pr₁ mp = ∥ ⟨ a ⟩' mp + ⟨ b ⟩' mp ∥
(a ||'' b) .pr₂ mp = ∥∥-is-prop


_||_ : BSet → BSet → BSet
⟨ a || b ⟩ mp = ⟨ a && b ⟩ mp + ⟨ ¬ᵇ (a && b) ⟩ mp × (⟨ a ⟩ mp + ⟨ b ⟩ mp)
-is-prop (a || b) mp (inl x) (inl y) = ap inl ((a && b) .-is-prop mp x y)
-is-prop (a || b) mp (inl x) (inr y) = 𝟘-elim (pr₁ y x)
-is-prop (a || b) mp (inr x) (inl y) = 𝟘-elim (pr₁ x y)
-is-prop (a || b) mp (inr x) (inr y) = ap inr ((a |x| b) .-is-prop mp x y)


Varᵇ : 𝓤 ⁺ ̇
Varᵇ = Σ D ꞉ 𝓤 ̇  , (D → BSet')

Var→BSet : Varᵇ → BSet'
Var→BSet (D , f) = (λ mp → ∥ (Σ x ꞉ D , ⟨ f x ⟩' mp) ∥) , (λ mp → ∥∥-is-prop)

-- Without prop or truncation, it is used in _&ᶠ_ to introduce the variance that
-- was introduced when sending the msg whose contents we do not know.
Varᵇ→Set : Varᵇ → Msg → 𝓤 ̇
Varᵇ→Set (D , f) mp = (Σ x ꞉ D , ⟨ f x ⟩' mp)


DVarᵇ : 𝓤 ⁺ ̇
DVarᵇ = Σ D ꞉ 𝓤 ̇  , (D → BSet' × BSet')

-- Redundant
DVar→BSet : DVarᵇ → BSet' × BSet'
DVar→BSet (D , f) = Var→BSet (D , pr₁ ∘ f) , Var→BSet (D , pr₂ ∘ f)

DVarᵇ→Set : DVarᵇ → Msg → 𝓤 ̇
DVarᵇ→Set (D , f) mp = Varᵇ→Set (D , pr₁ ∘ f) mp × Varᵇ→Set (D , pr₂ ∘ f) mp
