{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (𝟚)
open import MLTT.Negation
open import MLTT.Empty
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
open import UF.Retracts
open import Naturals.Order

module Secret2 (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) (Msg : 𝓤 ̇) where

module _ (Secret : 𝓤 ̇ ) where

 record W : 𝓤 ̇  where
  field
   f : ℕ → Secret
   neqf : is-section f


 Greater : (iw lw : W) → ℕ → 𝓤 ̇
 Greater iw lw m = ∀ x y → x ≤ℕ m → ¬ (iw .f x ＝ lw .f y ) where
  open W


 Neq : (w1 w2 : W) → 𝓤 ̇
 Neq w1 w2 = ∀ x y → ¬ (w1 .f x ＝ w2 .f y) where
  open W


-- We need to put this as a proposition to show that the way we split W is not important.
 record Split (ow w1 w2 : W) (m : ℕ) : 𝓤 ̇  where
  open W
  field
   ≤-neq1 : Greater ow w1 m
   ≤-neq2 : Greater ow w2 m
   neq : Neq w1 w2

 
-- Do we need associativity if we prove things abstractly ?
-- associativity
  -- record dfsdf : ? where
  --  field
  --   q : W → 
