{-# OPTIONS --safe --without-K --exact-split #-}


open import UF.FunExt

module Terminal (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties
open import UF.Equiv
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import UF.Subsingletons-FunExt
open import UF.Equiv-FunExt

open import Categories.Category fe
open import Categories.Functor fe

module _ {𝓤 𝓥} (c : precategory 𝓤 𝓥) where
 private
  module C = precategory c

 terminal : (𝓤 ⊔ 𝓥) ̇
 terminal = Σ t ꞉ C.ob , (∀ a → is-singleton (C.hom a t))
