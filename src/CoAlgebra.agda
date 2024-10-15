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

module CoAlgebra (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence)
                 {𝓥} {𝓦} {𝓣} (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  )
                 (dec : (a b : Secret) → is-decidable (a ＝ b)) where


open list-decidable dec

open PropositionalTruncation pt
open import UF.ImageAndSurjection pt

open import xBSet fe pt Msg Secret
open import &PSet (𝟚 × ×BSet 𝓥) pt
open import PSet pt (&PSet 𝓦 × &PSet 𝓦) 
open import Scope fe pt Msg Secret

ExC : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦' ̇  → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦' ̇
ExC X = ( Σ B ꞉ ×BSet 𝓥 × ×BSet 𝓥 , (∀ x → ⟨ B .pr₁ .pr₁ ⟩ x + ⟨ B .pr₂ .pr₁ ⟩ x → X))


-- TODO Move these two to the Operators file
ExCG : ∀ 𝓣 → 𝓦' ̇   → 𝓦' ⊔ (𝓣 ⁺) ̇
ExCG 𝓣 X = Σ D ꞉ 𝓣 ̇  , (D → X)

ExC→G : ∀ X → ExC {𝓦'} X → ExCG _ X
ExC→G X (a , b) = (Σ x ꞉ S×Msg , ⟨ (pr₁ ∘ pr₁) a ⟩ x + ⟨ (pr₁ ∘ pr₂) a ⟩ x) , λ (x , p) → b x p

-- We define the coalgebra of a functor F

-- This is a functor
F : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇  → (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺) ̇
F X = PSet 𝓣 × X × ExC {𝓦 ⁺ ⊔ 𝓣 ⁺} X

Fm : ∀{X Y} → (f : X → Y) → F X → F Y
Fm f (p , x , (bset , g)) = p , f x , (bset , (λ x bs → f (g x bs)))

Fm-comp :  ∀{X Y Z :  𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇ } → (f : X → Y) → (g : Z → X) → ∀ x → (Fm f) (Fm g x) ＝ Fm (f ∘ g) x
Fm-comp f g x = refl

Fm-id : ∀{X :  𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇ } → Fm id ∼ id {X = F X}
Fm-id x = refl

-- CoAlgebra

CoAlgebra : (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺)⁺ ̇
CoAlgebra = Σ E ꞉ 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇ , (E → F E)

module CoAlgebra (c : CoAlgebra) where
 E = c .pr₁
 f = c .pr₂


module CoAlgebra-morphism (b a : CoAlgebra) where
 private
  module A = CoAlgebra a
  module B = CoAlgebra b

 coalg-morphism : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇
 coalg-morphism = Σ f ꞉ (a .pr₁ → b .pr₁) , Fm f ∘ A.f ＝ B.f ∘ f

open CoAlgebra-morphism public

-- Final Coalgebra universal property

module Final-CoAlgebra-universal (final-co : CoAlgebra) where
 open CoAlgebra

 uniT : 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺⁺ ⊔ 𝓣 ⁺⁺ ̇
 uniT = ∀ a → (mo1 mo2 : coalg-morphism final-co a) → pr₁ mo1 ＝ pr₁ mo2 

record Final-CoAlgebra : {!!} ̇  where
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

-- module co-iso (fc : Final-CoAlgebra) where
--  module Q = Final-CoAlgebra fc
--  open CoAlgebra
--  open CoAlgebra-morphism

--  f-co : CoAlgebra
--  E f-co = F Q.E
--  f f-co = Fm Q.f

--  inv-morph : _
--  inv-morph = Q.uni f-co

--  inv = inv-morph .pr₁ .pr₁

--  morph : Σ (coalg-morphism Q.co Q.co)
--  pr₁ morph = inv ∘ Q.f
--  di-comm (pr₂ morph) =  dfunext fe (λ x → Fm-comp (pr₁ (inv-morph .pr₁)) Q.f (Q.f x)) ⁻¹ ∙ ap (_∘ Q.f) (inv-morph .pr₁ .pr₂ .di-comm) 


--  morph-Id : Σ (coalg-morphism Q.co Q.co)
--  pr₁ morph-Id = λ x → x
--  di-comm (pr₂ morph-Id) with (Fm {X = Q.E} id) | dfunext fe (Fm-id {X = Q.E})
--  ... | _ | refl = refl

--  inv∘Qf=id : inv ∘ Q.f ＝ (λ x → x)
--  inv∘Qf=id = l2 ⁻¹ ∙ l3 where
--   l1 = Q.uni Q.co
--   C = pr₁ l1
--   l2 : pr₁ C ＝ pr₁ morph
--   l2 = pr₂ l1 morph

--   l3 : pr₁ C ＝ pr₁ morph-Id
--   l3 = pr₂ l1 morph-Id

--  Qf∘inv=id : Q.f ∘ inv ＝ (λ x → x)
--  Qf∘inv=id = inv-morph .pr₁ .pr₂ .di-comm ⁻¹ ∙ (dfunext fe (λ x → Fm-comp (pr₁ (inv-morph .pr₁)) Q.f x) ∙ (ap Fm inv∘Qf=id ∙ dfunext fe Fm-id))

--  QE=FQE : Q.E ＝ F Q.E
--  QE=FQE = eqtoid (UA _) Q.E (F Q.E) (qinveq Q.f (inv , (λ x → ap (λ f → f x) inv∘Qf=id) , (λ x → ap (λ f → f x) Qf∘inv=id)))

-- module prod (fc : Final-CoAlgebra) where

--  module Q = Final-CoAlgebra fc
--  open CoAlgebra
--  open CoAlgebra-morphism
