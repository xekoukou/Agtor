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

module SCoAlgebra (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) (Msg : 𝓤 ̇) where

open PropositionalTruncation pt
open import BSet fe pt Msg
open import PSet fe pt Msg

ExCG : 𝓤 ⁺⁺ ̇  → 𝓤 ⁺⁺ ̇
ExCG X = Σ D ꞉ 𝓤 ̇  , (D → X)

ExC : 𝓤 ⁺⁺ ̇  → 𝓤 ⁺⁺ ̇
ExC X = ( Σ B ꞉ BSet × BSet , (∀ x → ⟨ B .pr₁ ⟩ x + ⟨ B .pr₂ ⟩ x → X))

ExC→G : ∀ X → ExC X → ExCG X
ExC→G X (a , b) = (Σ x ꞉ Msg , ⟨ pr₁ a ⟩ x + ⟨ pr₂ a ⟩ x) , λ (x , p) → b x p

-- We define the coalgebra of a functor F

-- We may need to add all the secrets here as well, for every part of the type and state to use it.
-- both the PSet and the two types.

-- This is a functor
F : 𝓤 ⁺⁺ ̇  → 𝓤 ⁺⁺ ̇
F X = PSet × X × ExC X

Fm : ∀{X Y} → (f : X → Y) → F X → F Y
Fm f (p , x , (bset , g)) = p , f x , (bset , (λ x bs → f (g x bs)))

-- CoAlgebra

record CoAlgebra : 𝓤 ⁺⁺ ⁺ ̇  where
 field
  E : 𝓤 ⁺⁺ ̇
  f : E → F E


module CoAlgebra-morphism (b a : CoAlgebra) where
 private
  module A = CoAlgebra a
  module B = CoAlgebra b

 record coalg-morphism (f : A.E → B.E) : 𝓤 ⁺⁺ ̇  where
  constructor co-morph 
  field
   di-comm : Fm f ∘ A.f ＝ B.f ∘ f

 open coalg-morphism public
 
-- Final Coalgebra universal property

module Final-CoAlgebra-universal (final-co : CoAlgebra) where
 open CoAlgebra
 open CoAlgebra-morphism final-co

 uniT : 𝓤 ⁺⁺ ⁺ ̇
 uniT = ∀ a → Σ mo ꞉ Σ (coalg-morphism a) , ((b : Σ (coalg-morphism a)) → pr₁ mo ＝ pr₁ b) 

record Final-CoAlgebra : 𝓤 ⁺⁺ ⁺ ̇  where
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
 di-comm (pr₂ morph) = ap (_∘ Q.f) (inv-morph .pr₁ .pr₂ .di-comm) 

 morph-Id : Σ (coalg-morphism Q.co Q.co)
 pr₁ morph-Id = λ x → x
 di-comm (pr₂ morph-Id) = refl

 inv∘Qf=id : inv ∘ Q.f ＝ (λ x → x)
 inv∘Qf=id = l2 ⁻¹ ∙ l3 where
  l1 = Q.uni Q.co
  C = pr₁ l1
  l2 : pr₁ C ＝ pr₁ morph
  l2 = pr₂ l1 morph

  l3 : pr₁ C ＝ pr₁ morph-Id
  l3 = pr₂ l1 morph-Id

 Qf∘inv=id : Q.f ∘ inv ＝ (λ x → x)
 Qf∘inv=id = inv-morph .pr₁ .pr₂ .di-comm ⁻¹ ∙ ap Fm inv∘Qf=id

 QE=FQE : Q.E ＝ F Q.E
 QE=FQE = eqtoid (UA _) Q.E (F Q.E) (qinveq Q.f (inv , (λ x → ap (λ f → f x) inv∘Qf=id) , (λ x → ap (λ f → f x) Qf∘inv=id)))

module prod (fc : Final-CoAlgebra) where

 module Q = Final-CoAlgebra fc
 open CoAlgebra
 open CoAlgebra-morphism

 

module embed (fc : Final-CoAlgebra) where
 open co-iso fc

 open CoAlgebra
 open CoAlgebra-morphism


-- This function combines the variance introduced by a function and the parallel composition
-- of two systems. We need to define it this way, because parallel composition
-- introduces this variance when the two systems interact with each other
 ExCGP : ExCG (F Q.E × F Q.E) → F (ExCG (F Q.E × F Q.E))
 -- The PSet
 pr₁ (ExCGP (D , var)) = &ᵈᵖ (D , λ d → (pr₁ (pr₁ (var d))) , ((pr₁ (pr₂ (var d)))))
 
 pr₁ (pr₂ (ExCGP (D , var))) = (Σ d ꞉ D , (𝟚 + Σ ⟨ bax d && bmy d ⟩ + Σ ⟨ bay d && bmx d ⟩)) , λ { (d , inl ₀) → x d , Q.f (iy d)
     ; (d , inl ₁) → y d , Q.f (ix d)
     ; (d , inr (inl (mp , (xa , ym)))) → (Q.f (pr₂ (nxcf d) mp (inl xa))) , (Q.f (pr₂ (nycf d) mp (inr ym)))
     ; (d , inr (inr (mp , (ya , xm)))) → (Q.f (pr₂ (nxcf d) mp (inr xm))) , (Q.f (pr₂ (nycf d) mp (inl ya)))} where
  nxcf : D → ExC Q.E
  nxcf d = pr₂ (pr₂ (pr₁ (var d)))
  nycf : D → ExC Q.E
  nycf d = pr₂ (pr₂ (pr₂ (var d)))

  bax : D → BSet
  bax d = pr₁ (pr₁ (nxcf d))
  bmx : D → BSet
  bmx d = pr₂ (pr₁ (nxcf d))

  bay : D → BSet
  bay d = pr₁ (pr₁ (nycf d))
  bmy : D → BSet
  bmy d = pr₂ (pr₁ (nycf d))

  y : D → F Q.E
  y d = pr₂ (var d)

  x : D → F Q.E
  x d = pr₁ (var d)

  iy : D → Q.E
  iy d = pr₁ (pr₂ (pr₂ (var d)))
 
  ix : D → Q.E
  ix d = pr₁ (pr₂ (pr₁ (var d)))

 pr₂ (pr₂ (ExCGP (D , var))) = e where
  nxcf : D → ExC Q.E
  nxcf d = pr₂ (pr₂ (pr₁ (var d)))
  nycf : D → ExC Q.E
  nycf d = pr₂ (pr₂ (pr₂ (var d)))

  y : D → F Q.E
  y d = pr₂ (var d)

  x : D → F Q.E
  x d = pr₁ (var d)

  bax : D → BSet
  bax d = pr₁ (pr₁ (nxcf d))
  bmx : D → BSet
  bmx d = pr₂ (pr₁ (nxcf d))

  bay : D → BSet
  bay d = pr₁ (pr₁ (nycf d))
  bmy : D → BSet
  bmy d = pr₂ (pr₁ (nycf d))

  ba : BSet
  ⟨ ba ⟩ mp = ∥ Σ d ꞉ D , ⟨ (bax d) || (bay d) ⟩ mp ∥
  -is-prop ba mp = ∥∥-is-prop

  bm : BSet
  ⟨ bm ⟩ mp = ∥ Σ d ꞉ D , ⟨ (bmx d) || (bmy d) ⟩ mp ∥
  -is-prop bm mp = ∥∥-is-prop

  e : ExC (ExCG (F Q.E × F Q.E))
  pr₁ e = ba , bm
  pr₂ e mp (inl v)
    =   (Σ d ꞉ D , ⟨ bax d ⟩ mp + ⟨ bay d ⟩ mp)
      , λ { (d , inl px) → Q.f (pr₂ (nxcf d) mp (inl px)) , (y d)
          ; (d , inr py) → Q.f (pr₂ (nycf d) mp (inl py)) , (x d)}
  pr₂ e mp (inr w)
    =   (Σ d ꞉ D , ⟨ bmx d ⟩ mp + ⟨ bmy d ⟩ mp)
      , λ { (d , inl px) → Q.f (pr₂ (nxcf d) mp (inr px)) , (y d)
          ; (d , inr py) → Q.f (pr₂ (nycf d) mp (inr py)) , (x d)}


 ExCGP-co : CoAlgebra
 E ExCGP-co = ExCG (F Q.E × F Q.E)
 f ExCGP-co = ExCGP

 _&ᶠ_ : Q.E → Q.E → Q.E
 a &ᶠ b = Q.uni ExCGP-co .pr₁ .pr₁ (𝟙 , (λ x → Q.f a , Q.f b))




 ∣P' : ExCG (F Q.E) → F (ExCG (F Q.E))
 pr₁ (∣P' (D , f)) = Var→PSet (D , pr₁ ∘ f)
 pr₁ (pr₂ (∣P' (D , f))) = D , (Q.f ∘ pr₁ ∘ pr₂ ∘ f)
 pr₂ (pr₂ (∣P' (D , f)))
  =   (DVar→×BSet (_ , λ d → (pr₁ ∘ pr₂ ∘ pr₂ ∘ f) d))
    , λ { mp (inl _) →   Varᵇ→Set (D , (pr₁ ∘ pr₁ ∘ pr₂ ∘ pr₂ ∘ f)) mp
                       , λ { (d , v) → Q.f ((pr₂ ∘ pr₂ ∘ pr₂ ∘ f) d mp (inl v))}
        ; mp (inr _) →   Varᵇ→Set (D , (pr₂ ∘ pr₁ ∘ pr₂ ∘ pr₂ ∘ f)) mp
                       , λ { (d , v) → Q.f ((pr₂ ∘ pr₂ ∘ pr₂ ∘ f) d mp (inr v))}}

 --Maybe this is easier to understand.
 -- With this definition, one understands that when we receive a msg, we actually also learn something about the prior superposition. The previous definition does not make this clear.
 ∣P : (F Q.E + 𝟙 {𝓤}) × F Q.E → F ((F Q.E + 𝟙 {𝓤}) × F Q.E)
 ∣P (inl (px , x , (bax , bmx) , fx) , (py , y , (bay , bmy) , fy))
   =   (px ∣ᵖ py)
     , ((inl (Q.f x)) ,   (Q.f y))
     , ((bax || bay) , (bmx || bmy))
       , (λ { x (inl (inl (vx , vy))) → inl (Q.f (fx x (inl vx))) , Q.f (fy x (inl vy)) 
            ; x (inl (inr (_ , inl vx))) → inr ⋆ , Q.f (fx x (inl vx))
            ; x (inl (inr (_ , inr vy))) → inr ⋆ , Q.f (fy x (inl vy))
            ; x (inr (inl (vx , vy))) → inl (Q.f (fx x (inr vx))) , Q.f (fy x (inr vy)) 
            ; x (inr (inr (_ , inl vx))) → inr ⋆ , Q.f (fx x (inr vx))
            ; x (inr (inr (_ , inr vy))) → inr ⋆ , Q.f (fy x (inr vy))
            })
 ∣P (inr _ , (py , y , (bay , bmy) , fy)) = py , ((inr ⋆) , (Q.f y)) , ((bay , bmy) , (λ x p → (inr ⋆) , (Q.f (fy x p))))


 ∣P'-co : CoAlgebra
 E ∣P'-co = ExCG (F Q.E)
 f ∣P'-co = ∣P'

 _∣ᶠ_ : Q.E → Q.E → Q.E
 a ∣ᶠ b = Q.uni ∣P'-co .pr₁ .pr₁ ((𝟙 {𝓤} + 𝟙 {𝓤}) , (λ { (inl _) → Q.f a ; (inr _) → Q.f b}))

