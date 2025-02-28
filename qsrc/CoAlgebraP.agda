{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

module CoAlgebraP where

open import FunctorP

CoAlgebra : (func : Functor 𝓤) → 𝓤 ⁺ ̇
CoAlgebra func = Σ A ꞉ _ , (A → F.Fn A) where
 private
  module F = Functor func 


module CoAlgebra func (co : CoAlgebra {𝓤} func) where

 open Functor func

 type : 𝓤 ̇ 
 type = co .pr₁

 morph : type → Fn type
 morph = co .pr₂

module CoAlgebra₂ func (a b : CoAlgebra {𝓤} func) where
 open Functor func

 private
  module A = CoAlgebra func a
  module B = CoAlgebra func b

 f-co-morphism : 𝓤 ̇
 f-co-morphism = Σ f ꞉ (A.type → B.type) , Fm f ∘ A.morph ∼ B.morph ∘ f

 module Morphism (m : f-co-morphism) where
  morphism : A.type → B.type
  morphism = m .pr₁

  property : Fm morphism ∘ A.morph ∼ B.morph ∘ morphism
  property = m .pr₂
 
