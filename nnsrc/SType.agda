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
open import MLTT.Two renaming (₀ to 𝕞 ; ₁ to 𝕒)

open import Free

module SType (fe : Fun-Ext) (Msg : 𝓤 ̇) where

open import BSet fe Msg
open BSet

module _ (s : free-comm-sgroup {𝓤 = 𝓤} (𝟚 × BSet)) where

 module O = free-comm-sgroup s

 -- This predicate describes all the possible superpositions of a system.
 record PSet : 𝓤 ⁺ ̇  where
  field
   ⟨_⟩ : (o : O.E) → 𝓤 ̇ 
   -is-prop : ∀ o → is-prop (⟨_⟩ o)


-- We define the coalgebra of a functor F

-- This is a functor
 F : 𝓤 ⁺ ̇  → 𝓤 ⁺ ̇
 F X = PSet × X × ( Σ B ꞉ BSet , (∀ x → ⟨ B ⟩ x → X))
 -- This does not need to be a BSet m, no need for decidability
 
 Fm : ∀{X Y} → (f : X → Y) → F X → F Y
 Fm f (p , x , (bset , g)) = p , f x , bset , (λ x bs → f (g x bs))


-- CoAlgebra

 record CoAlgebra : 𝓤 ⁺⁺ ̇  where
  field
   E : 𝓤 ⁺ ̇
   f : E → F E
   

 module CoAlgebra-morphism (a b : CoAlgebra) where
  module A = CoAlgebra a
  module B = CoAlgebra b

  record coalg-morphism : 𝓤 ⁺ ̇  where
   field
    f : A.E → B.E
    Ff : F A.E → F B.E
    di-comm : Ff ∘ A.f ＝ B.f ∘ f
 

-- Final Coalgebra universal property

 module Final-CoAlgebra-universal (final-co : CoAlgebra) where
  open CoAlgebra-morphism final-co

  uniT : 𝓤 ⁺⁺ ̇
  uniT = ∀ a → coalg-morphism a
 
 record Final-Coalgebra : 𝓤 ⁺⁺ ̇  where
  field
   co : CoAlgebra
  open CoAlgebra
  open Final-CoAlgebra-universal co
  field
   uni : uniT

