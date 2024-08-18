{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (𝟚)
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import UF.Univalence
open import UF.Equiv
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Base

open import Lists
open import Maybe

-- I know that UA proves Prop-Ext
module xBSet (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) (s-is-set : is-set Secret) (dec : (a b : Secret) → is-decidable (a ＝ b)) where

open PropositionalTruncation pt

S×Msg : 𝓤 ̇
S×Msg = List Secret × (Msg + Secret)

open import BSet fe pt S×Msg public

-- We have propositional equality which can be derived from (A → B , B → A)
_⇔_ : (A B : 𝓤 ̇) → 𝓤 ̇
A ⇔ B = (A → B) × (B → A)

×BSet : 𝓤 ⁺ ̇
×BSet = Σ bs ꞉ BSet , ∀ ascrs scrs x → scrs ⊃ ascrs × ascrs ⊃ scrs → ⟨ bs ⟩ (ascrs , x) ⇔ (⟨ bs ⟩ (scrs , x))

_bset : ×BSet → BSet
_bset bs = bs .pr₁

-- The property holds for all messages.
×⊨ : ×BSet → 𝓤 ̇
×⊨ P = ∀ a → ⟨ P bset ⟩ a 

×⊥B : ×BSet
×⊥B = ⊥B , λ ascrs scrs _ _ → id , id

×⊤B : ×BSet
×⊤B = ⊤B , λ ascrs scrs _ _ → id , id

-- _⟶_ : BSet → BSet → BSet
-- ⟨ P ⟶ Q ⟩ mp = ⟨ P ⟩ mp → ⟨ Q ⟩ mp
-- (P ⟶ Q) .-is-prop mp = Π-is-prop fe (λ _ → (Q .-is-prop) mp)
-- -- (P ⟶ Q) .-is-decidable mp with Q .-is-decidable mp
-- -- ... | inl q = inl λ _ → q
-- -- ... | inr q with P .-is-decidable mp
-- -- ... | inl p = inr λ x → q (x p)
-- -- ... | inr p = inl (λ x → 𝟘-elim (p x))

_×&&_ : ×BSet → ×BSet → ×BSet
a ×&& b
 =   ((a bset) && (b bset))
   , λ ascrs scrs x eq → (λ (z , y) → (a .pr₂ scrs ascrs x ((eq .pr₂) , (eq .pr₁)) .pr₂ z) , (b .pr₂ scrs ascrs x ((eq .pr₂) , (eq .pr₁)) .pr₂ y))
   , λ (z , y) → (a .pr₂ ascrs scrs x eq .pr₂ z) , (b .pr₂ ascrs scrs x eq .pr₂ y)

-- _≡ᵇ_ : BSet → BSet → 𝓤 ̇
-- A ≡ᵇ B = ⊨ ((A ⟶ B) && (B ⟶ A))

-- ¬ᵇ : BSet → BSet
-- ⟨ ¬ᵇ A ⟩ mp = ¬ (⟨ A ⟩ mp)
-- -is-prop (¬ᵇ A) mp = Π-is-prop fe λ _ → 𝟘-is-prop
-- -- -is-decidable (¬ᵇ A) mp with -is-decidable A mp
-- -- ... | inl x = inr (λ ¬f → ¬f x)
-- -- ... | inr x = inl x

-- -- I do not like this definition, because we need to prove the negation
-- --  update : But since we have decidability anyway, this is provable immediately
-- _─_ : BSet → BSet → BSet
-- (a ─ b) = a && (¬ᵇ b)

-- _|x|_ : BSet → BSet → BSet
-- ⟨ a |x| b ⟩ mp = ⟨ ¬ᵇ (a && b) ⟩ mp × (⟨ a ⟩ mp + ⟨ b ⟩ mp)
-- -is-prop (a |x| b) mp
--  = Σ-is-prop
--     (¬ᵇ (a && b) .-is-prop mp)
--     (λ ¬pa&b → +-is-prop (a .-is-prop mp)
--     (b .-is-prop mp)
--     λ pa pb → ¬pa&b (pa , pb))
-- -- -is-decidable (a |x| b) mp with a .-is-decidable mp | b .-is-decidable mp
-- -- ... | inl x | inl y = inr (λ (z , _) → z (x , y))
-- -- ... | inl x | inr y = inl ((λ (_ , e) → y e) , inl x)
-- -- ... | inr x | inl y = inl ((λ (e , _) → x e) , inr y)
-- -- ... | inr x | inr y = inr λ { (_ , inl z) → x z ; (_ , inr z) → y z}

-- -- I use this definition because of the proof of is-prop
-- _||'_ : BSet → BSet → BSet
-- a ||' b = (a && b) |x| (a |x| b)


-- _||_ : BSet → BSet → BSet
-- ⟨ a || b ⟩ mp = ⟨ a && b ⟩ mp + ⟨ ¬ᵇ (a && b) ⟩ mp × (⟨ a ⟩ mp + ⟨ b ⟩ mp)
-- -is-prop (a || b) mp (inl x) (inl y) = ap inl ((a && b) .-is-prop mp x y)
-- -is-prop (a || b) mp (inl x) (inr y) = 𝟘-elim (pr₁ y x)
-- -is-prop (a || b) mp (inr x) (inl y) = 𝟘-elim (pr₁ x y)
-- -is-prop (a || b) mp (inr x) (inr y) = ap inr ((a |x| b) .-is-prop mp x y)


-- Varᵇ : 𝓤 ⁺ ̇
-- Varᵇ = Σ D ꞉ 𝓤 ̇  , (D → BSet)

-- Var→BSet : Varᵇ → BSet
-- ⟨ Var→BSet (D , f) ⟩ mp = ∥ (Σ x ꞉ D , ⟨ f x ⟩ mp) ∥
-- -is-prop (Var→BSet (d , f)) _ = ∥∥-is-prop

-- Varᵇ→Set : Varᵇ → Msg → 𝓤 ̇
-- Varᵇ→Set (D , f) mp = (Σ x ꞉ D , ⟨ f x ⟩ mp)


-- DVarᵇ : 𝓤 ⁺ ̇
-- DVarᵇ = Σ D ꞉ 𝓤 ̇  , (D → BSet × BSet)

-- -- Redundant
-- DVar→×BSet : DVarᵇ → BSet × BSet
-- DVar→×BSet (D , f) = Var→BSet (D , pr₁ ∘ f) , Var→BSet (D , pr₂ ∘ f)

-- DVarᵇ→Set : DVarᵇ → Msg → 𝓤 ̇
-- DVarᵇ→Set (D , f) mp = Varᵇ→Set (D , pr₁ ∘ f) mp × Varᵇ→Set (D , pr₂ ∘ f) mp

-- -- -- We do not use this because we have decidability of prop
-- -- _||_ : BSet → BSet → BSet
-- -- ⟨ a || b ⟩ mp = ∥ ⟨ a ⟩ mp + ⟨ b ⟩ mp ∥
-- -- (a || b) .-is-prop mp = ∥∥-is-prop
-- -- (a || b) .-is-decidable mp with a .-is-decidable mp | b .-is-decidable mp
-- -- ... | inl x | q = inl ∣ inl x ∣
-- -- ... | inr x | inl y = inl ∣ inr y ∣
-- -- ... | inr x | inr y = inr (∥∥-rec 𝟘-is-prop (λ { (inl z) → x z
-- --                                                ; (inr z) → y z}))

