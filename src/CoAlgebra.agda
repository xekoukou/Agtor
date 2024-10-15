{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
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

module CoAlgebra (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) (dec : (a b : Secret) → is-decidable (a ＝ b)) where


open list-decidable dec

open PropositionalTruncation pt
open import UF.ImageAndSurjection pt

open import xBSet fe pt Msg Secret
open import &PSet (𝟚 × ×BSet) pt
open import PSet pt (&PSet × &PSet) (λ (a1 , a2) (b1 , b2) → (a1 &-&ᵖ b1) , ((a2 &-&ᵖ b2)))
open import Scope fe pt Msg Secret

-- non-empty variance
ExCG : 𝓤 ⁺⁺ ⁺ ̇  → 𝓤 ⁺⁺ ⁺ ̇
ExCG X = Σ D ꞉ 𝓤 ̇  , (D → X)

ExC : 𝓤 ⁺⁺ ⁺ ̇  → 𝓤 ⁺⁺ ⁺ ̇
ExC X = ( Σ B ꞉ ×BSet × ×BSet , (∀ x → ⟨ B .pr₁ .pr₁ ⟩ x + ⟨ B .pr₂ .pr₁ ⟩ x → X))

ExC→G : ∀ X → ExC X → ExCG X
ExC→G X (a , b) = (Σ x ꞉ S×Msg , ⟨ (pr₁ ∘ pr₁) a ⟩ x + ⟨ (pr₁ ∘ pr₂) a ⟩ x) , λ (x , p) → b x p

-- We define the coalgebra of a functor F

-- This is a functor
F : 𝓤 ⁺⁺ ⁺ ̇  → 𝓤 ⁺⁺ ⁺ ̇
F X = PSet × X × ExC X

Fm : ∀{X Y} → (f : X → Y) → F X → F Y
Fm f (p , x , (bset , g)) = p , f x , (bset , (λ x bs → f (g x bs)))

Fm-comp :  ∀{X Y Z : 𝓤 ⁺⁺ ⁺ ̇} → (f : X → Y) → (g : Z → X) → ∀ x → (Fm f) (Fm g x) ＝ Fm (f ∘ g) x
Fm-comp f g x = refl

Fm-id : ∀{X : 𝓤 ⁺⁺ ⁺ ̇} → Fm id ∼ id {X = F X}
Fm-id x = refl

-- CoAlgebra

record CoAlgebra : 𝓤 ⁺⁺ ⁺⁺ ̇  where
 field
  E : 𝓤 ⁺⁺ ⁺ ̇
  f : E → F E


module CoAlgebra-morphism (b a : CoAlgebra) where
 private
  module A = CoAlgebra a
  module B = CoAlgebra b

 record coalg-morphism (f : A.E → B.E) : 𝓤 ⁺⁺ ⁺ ̇  where
  constructor co-morph 
  field
   di-comm : Fm f ∘ A.f ＝ B.f ∘ f

 open coalg-morphism public
 
-- Final Coalgebra universal property

module Final-CoAlgebra-universal (final-co : CoAlgebra) where
 open CoAlgebra
 open CoAlgebra-morphism final-co

 uniT : 𝓤 ⁺⁺ ⁺⁺ ̇
 uniT = ∀ a → Σ mo ꞉ Σ (coalg-morphism a) , ((b : Σ (coalg-morphism a)) → pr₁ mo ＝ pr₁ b) 

record Final-CoAlgebra : 𝓤 ⁺⁺ ⁺⁺ ̇  where
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

module co-iso (fc : Final-CoAlgebra) where
 module Q = Final-CoAlgebra fc
 open CoAlgebra
 open CoAlgebra-morphism

 f-co : CoAlgebra
 E f-co = F Q.E
 f f-co = Fm Q.f

 inv-morph : _
 inv-morph = Q.uni f-co

 inv = inv-morph .pr₁ .pr₁

 morph : Σ (coalg-morphism Q.co Q.co)
 pr₁ morph = inv ∘ Q.f
 di-comm (pr₂ morph) =  dfunext fe (λ x → Fm-comp (pr₁ (inv-morph .pr₁)) Q.f (Q.f x)) ⁻¹ ∙ ap (_∘ Q.f) (inv-morph .pr₁ .pr₂ .di-comm) 


 morph-Id : Σ (coalg-morphism Q.co Q.co)
 pr₁ morph-Id = λ x → x
 di-comm (pr₂ morph-Id) with (Fm {X = Q.E} id) | dfunext fe (Fm-id {X = Q.E})
 ... | _ | refl = refl

 inv∘Qf=id : inv ∘ Q.f ＝ (λ x → x)
 inv∘Qf=id = l2 ⁻¹ ∙ l3 where
  l1 = Q.uni Q.co
  C = pr₁ l1
  l2 : pr₁ C ＝ pr₁ morph
  l2 = pr₂ l1 morph

  l3 : pr₁ C ＝ pr₁ morph-Id
  l3 = pr₂ l1 morph-Id

 Qf∘inv=id : Q.f ∘ inv ＝ (λ x → x)
 Qf∘inv=id = inv-morph .pr₁ .pr₂ .di-comm ⁻¹ ∙ (dfunext fe (λ x → Fm-comp (pr₁ (inv-morph .pr₁)) Q.f x) ∙ (ap Fm inv∘Qf=id ∙ dfunext fe Fm-id))

 QE=FQE : Q.E ＝ F Q.E
 QE=FQE = eqtoid (UA _) Q.E (F Q.E) (qinveq Q.f (inv , (λ x → ap (λ f → f x) inv∘Qf=id) , (λ x → ap (λ f → f x) Qf∘inv=id)))

module prod (fc : Final-CoAlgebra) where

 module Q = Final-CoAlgebra fc
 open CoAlgebra
 open CoAlgebra-morphism
