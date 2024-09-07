{-# OPTIONS --safe --without-K --exact-split #-}


open import UF.FunExt

module Final-CoAlgebra (fe : Fun-Ext) where

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

open import CoAlgebra fe
open import Terminal fe

module _ {𝓤 𝓥} (c : precategory 𝓤 𝓥) where
 open functor-of-precategories c c

 private
  module C = precategory c

 module _ (fct : functor) where
  private
   module F = functor fct

  module PC = precategory (F-Coalgebra-precategory c fct)
