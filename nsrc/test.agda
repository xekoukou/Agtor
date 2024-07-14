{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (rec)
open import MLTT.List
open import MLTT.Maybe
open import MLTT.Bool
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
open import UF.Equiv
open import UF.Univalence
open import MLTT.Two renaming (₀ to 𝕞 ; ₁ to 𝕒)

open import Free

module test  (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓥 ̇ ) where

open import BSet fe pt Msg

open BSet


f : ∀ A → Bool ＝ A → (x : Bool) → A
f .Bool refl x = x





-- -- -- -- --   f = {!!}

   


-- -- -- -- -- -- module Context {𝓤} (Secret : 𝓤 ̇) where

-- -- -- -- -- --   Context : 𝓤 ⁺ ̇
-- -- -- -- -- --   Context = List (𝓤 ̇)

-- -- -- -- -- --   data diff-member : ∀ {ctx : Context} → member Secret ctx → member Secret ctx → 𝓤 ⁺ ̇  where
-- -- -- -- -- --     head-tail : {ctx : Context} → ∀{b : member Secret ctx} → diff-member in-head (in-tail b)
-- -- -- -- -- --     tail-head : {ctx : Context} → ∀{b : member Secret ctx} → diff-member (in-tail b) in-head
-- -- -- -- -- --     tail-tail : ∀{X} → {ctx : Context} → ∀{a b : member Secret ctx} → diff-member {ctx = X ∷ ctx} (in-tail a) (in-tail b)

-- -- -- -- -- --   -- In the context, we only store the Type, thus we need to introduce this elsewhere.
-- -- -- -- -- --   secrets-unique : Context → {!!}
-- -- -- -- -- --   secrets-unique ctx = (a b : member Secret ctx) → diff-member a b → {!!}

  
-- -- -- -- -- -- -- data _⊢_ : Context → Term
