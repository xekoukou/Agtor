{-# OPTIONS --without-K --exact-split #-}

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

module SType (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) where

open PropositionalTruncation pt
open import BSet fe Msg
open BSet

module _ (s : free-comm-sgroup {𝓤 = 𝓤} (𝟚 × BSet)) where

 module O = free-comm-sgroup s renaming (_*_ to _&_)

 -- This predicate describes all the possible superpositions of a system.
 record PSet : 𝓤 ⁺ ̇  where
  field
   ⟨_⟩ : (o : O.E) → 𝓤 ̇ 
   -is-prop : ∀ o → is-prop (⟨_⟩ o)

 module _ where
  open PSet
  
  _&ᵖ_ : PSet → PSet → PSet
  ⟨ A &ᵖ B ⟩ o = ∥ Σ x ꞉ O.E , Σ y ꞉ O.E , ⟨ A ⟩ x × ⟨ B ⟩ y × (x O.& y ＝ o) ∥
  ((A &ᵖ B) .-is-prop) o = ∥∥-is-prop

  _∣ᵖ_ : PSet → PSet → PSet
  ⟨ A ∣ᵖ B ⟩ o = ∥ ⟨ A ⟩ o + ⟨ B ⟩ o ∥
  -is-prop (A ∣ᵖ B) o = ∥∥-is-prop

 ExC : 𝓤 ⁺ ̇  → 𝓤 ⁺ ̇
 ExC X = ( Σ B ꞉ BSet × BSet , (∀ x → ⟨ B .pr₁ ⟩ x + ⟨ B .pr₂ ⟩ x → X))

-- We define the coalgebra of a functor F

-- We may need to add all the secrets here as well, for every part of the type and state to use it.
-- both the PSet and the two types.

-- This is a functor
 F : 𝓤 ⁺ ̇  → 𝓤 ⁺ ̇
 F X = PSet × X × ( Σ B ꞉ BSet × BSet , (∀ x → ⟨ B .pr₁ ⟩ x + ⟨ B .pr₂ ⟩ x → X))
 
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

  record coalg-morphism (f : A.E → B.E) : 𝓤 ⁺ ̇  where
   field
    di-comm : Fm f ∘ A.f ＝ B.f ∘ f
 

-- Final Coalgebra universal property

 module Final-CoAlgebra-universal (final-co : CoAlgebra) where
  open CoAlgebra-morphism final-co

  uniT : 𝓤 ⁺⁺ ̇
  uniT = ∀ a → ∃! (coalg-morphism a)
 
 record Final-CoAlgebra : 𝓤 ⁺⁺ ̇  where
  field
   co : CoAlgebra
  open CoAlgebra co public
  open Final-CoAlgebra-universal co public
  field
   uni : uniT


-- According to theorem 2.1 
-- https://ncatlab.org/nlab/show/terminal+coalgebra+for+an+endofunctor
-- F X is is isomorphic to X if X is a final coalgebra
-- TODO Check that this category is univalent and thus isomorphism leads to equalityz
-- The way we defined it , it is univalent, we are in the category of Sets and
-- we have the univalence theorem

 module _ (fc : Final-CoAlgebra) where
  module Q = Final-CoAlgebra fc

  postulate
  -- Make sure this is a unique homeomorphism, or that it does not interfere in any way..
  -- Due to uniqueness of the coalgebra morphism of the terminal object
  -- there is a unique isomophism.
  -- Any isomophism creates a coalgebraic morphism. 
   eqFQ : Q.E ＝ F Q.E

  {-# TERMINATING #-}
  _&ᶠ_ : (x y : Q.E) → Q.E
  _∣ᶠ_ : (x y : Q.E) → Q.E
  _∘∘_ : ExC Q.E → ExC Q.E → Q.E

  x &ᶠ y with transport (λ x → x) eqFQ x | transport (λ x → x) eqFQ y
  ... | (px , nx , tfx@(bsx , fx)) | (py , ny , tfy@(bsy , fy)) = transport (λ x → x) (eqFQ ⁻¹) ((px &ᵖ py) , (x &ᶠ ny) ∣ᶠ ((nx &ᶠ y) ∣ᶠ (tfx ∘∘ tfy)) , {!!}) 
 -- (px , nx , (bsx , fx)) &ᶠ y@(py , ny , (bsy , fy)) = (px &ᵖ py) , {!y &ᶠ (transport ? ? ?)!} , {!!}

  ((bsaA , bsmA) , A) ∘∘ ((bsaB , bsmB) , B)
   = transport (λ x → x) (eqFQ ⁻¹) ({!!} , {!!}) where
    nA : (x : Msg) → ⟨ bsaA ⟩ x + ⟨ bsmA ⟩ x → F Q.E
    nA x p = transport (λ x → x) eqFQ (A x p)
    nB : (x : Msg) → ⟨ bsaB ⟩ x + ⟨ bsmB ⟩ x → F Q.E
    nB x p = transport (λ x → x) eqFQ (B x p)

    pnA : (x : Msg) → ⟨ bsaA ⟩ x + ⟨ bsmA ⟩ x → PSet
    pnA x p = nA x p .pr₁
    pnB : (x : Msg) → ⟨ bsaB ⟩ x + ⟨ bsmB ⟩ x → PSet
    pnB x p = nB x p .pr₁

    pnA+B : (x : Msg) → ⟨ bsaA && bsmB ⟩ x + ⟨ bsmA && bsaB ⟩ x → Q.E
    pnA+B x (inl b→a) = {!? &ᶠ ?!}
    pnA+B x (inr a→b) = {!!}
