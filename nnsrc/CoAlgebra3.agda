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
open import MLTT.Two renaming (₀ to 𝕞 ; ₁ to 𝕒)


module CoAlgebra3 (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) (Msg : 𝓤 ̇) where

open PropositionalTruncation pt
open import BSet fe Msg
open import PSet fe pt Msg


ExC : 𝓤 ⁺⁺ ̇  → 𝓤 ⁺⁺ ̇
ExC X = ( Σ B ꞉ BSet × BSet , (∀ x → ⟨ B .pr₁ ⟩ x + ⟨ B .pr₂ ⟩ x → X))

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
 module A = CoAlgebra a
 module B = CoAlgebra b

 record coalg-morphism (f : A.E → B.E) : 𝓤 ⁺⁺ ̇  where
  constructor co-morph 
  field
   di-comm : Fm f ∘ A.f ＝ B.f ∘ f

 open coalg-morphism public
 
-- Final Coalgebra universal property

module Final-CoAlgebra-universal (final-co : CoAlgebra) where
 open CoAlgebra-morphism final-co

 uniT : 𝓤 ⁺⁺ ⁺ ̇
 uniT = ∀ a → ∃! (coalg-morphism a)

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

 inv-morph : is-singleton (Σ (coalg-morphism Q.co f-co))
 inv-morph = Q.uni f-co

 inv = inv-morph .pr₁ .pr₁

 morph : Σ (coalg-morphism Q.co Q.co)
 pr₁ morph = inv ∘ Q.f
 di-comm (pr₂ morph) = ap (_∘ Q.f) (inv-morph .pr₁ .pr₂ .di-comm) 

 morph-Id : Σ (coalg-morphism Q.co Q.co)
 pr₁ morph-Id = λ x → x
 di-comm (pr₂ morph-Id) = refl

 inv∘Qf=id : inv ∘ Q.f ＝ (λ x → x)
 inv∘Qf=id = ap pr₁ (singletons-are-props (Q.uni Q.co) morph morph-Id) 

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



 ExCP : ExC (F Q.E) → F (ExC (F Q.E))
 
 ∣⟨ pr₁ (ExCP ((bsa , bsm) , f)) ⟩ &ps
   = ∥ Σ x ꞉ Msg , Σ p ꞉ ⟨ bsa ⟩ x + ⟨ bsm ⟩ x , ∣⟨ pr₁ (f x p) ⟩ &ps ∥

 ∣-is-prop (pr₁ (ExCP f)) &ps = ∥∥-is-prop
 
 pr₁ (pr₂ (ExCP ((bsa , bsm) , f)))
   = (bsa  , bsm) , (λ x p → Q.f (pr₁ (pr₂ (f x p))))

 pr₂ (pr₂ (ExCP ((bsa , bsm) , f))) = (nbsa , nbsm) , e where
  fexc = λ x p → (pr₂ (pr₂ (f x p)))
  fbsa = λ x p → pr₁ (pr₁ (fexc x p))
  fbsm = λ x p → pr₂ (pr₁ (fexc x p))
  nbsa : BSet
  ⟨ nbsa ⟩ mp =  ∥ Σ x ꞉ Msg , Σ p ꞉ ⟨ bsa ⟩ x + ⟨ bsm ⟩ x ,   ⟨ fbsa x p ⟩ mp ∥
  -is-prop nbsa mp = ∥∥-is-prop
  nbsm : BSet
  ⟨ nbsm ⟩ mp =  ∥ Σ x ꞉ Msg , Σ p ꞉ ⟨ bsa ⟩ x + ⟨ bsm ⟩ x ,   ⟨ fbsm x p ⟩ mp ∥
  -is-prop nbsm mp = ∥∥-is-prop
  e : (mp : Msg) → ⟨ nbsa ⟩ mp + ⟨ nbsm ⟩ mp → ExC (F Q.E)
  e mp (inl pa) = ((nbsaa mp) , nbsam mp) , (λ { y (inl p) → Q.f (pr₂ (fexc y (inl (pr₁ p))) mp (inl (pr₂ p))) ; y (inr p) → Q.f (pr₂ (fexc y (inr (pr₁ p))) mp (inl (pr₂ p)))}) where
   nbsaa : Msg → BSet
   ⟨ nbsaa mp ⟩ x =  Σ p ꞉ ⟨ bsa ⟩ x ,   ⟨ fbsa x (inl p) ⟩ mp
   -is-prop (nbsaa mp) x = Σ-is-prop (bsa .-is-prop x) λ _ → fbsa x _ .-is-prop mp
   nbsam : Msg → BSet
   ⟨ nbsam mp ⟩ x =  Σ p ꞉ ⟨ bsm ⟩ x ,   ⟨ fbsa x (inr p) ⟩ mp
   -is-prop (nbsam mp) x = Σ-is-prop (bsm .-is-prop x) λ _ → fbsa x _ .-is-prop mp
  e mp (inr pm) = ((nbsma mp) , nbsmm mp) , (λ { y (inl p) → Q.f (pr₂ (fexc y (inl (pr₁ p))) mp (inr (pr₂ p))) ; y (inr p) → Q.f (pr₂ (fexc y (inr (pr₁ p))) mp (inr (pr₂ p)))}) where
   nbsma : Msg → BSet
   ⟨ nbsma mp ⟩ x =  Σ p ꞉ ⟨ bsa ⟩ x ,   ⟨ fbsm x (inl p) ⟩ mp
   -is-prop (nbsma mp) x = Σ-is-prop (bsa .-is-prop x) λ _ → fbsm x _ .-is-prop mp
   nbsmm : Msg → BSet
   ⟨ nbsmm mp ⟩ x =  Σ p ꞉ ⟨ bsm ⟩ x ,   ⟨ fbsm x (inr p) ⟩ mp
   -is-prop (nbsmm mp) x = Σ-is-prop (bsm .-is-prop x) λ _ → fbsm x _ .-is-prop mp

 coExC : CoAlgebra
 CoAlgebra.E coExC = ExC (F Q.E)
 CoAlgebra.f coExC = ExCP

-- Since Q is a terminal object, we have a coalgebraic morphism that embeds coExC into Q.

 exC-morph : _
 exC-morph = Q.uni coExC
 exC> = pr₁ (pr₁ exC-morph)



-- Either do that or use the ExC embedding.
--Maybe this is easier to understand.
 ∣P : (F Q.E + 𝟙 {𝓤}) × F Q.E → F ((F Q.E + 𝟙 {𝓤}) × F Q.E)
 ∣P (inl (px , x , (bax , bmx) , fx) , (py , y , (bay , bmy) , fy))
   =   (px ∣ᵖ py)
     , ((inl (Q.f x))
     ,   (Q.f y)) , ((bax || bay) , (bmx || bmy))
       , (λ { x (inl (inl (vx , vy))) → inl (Q.f (fx x (inl vx))) , Q.f (fy x (inl vy)) 
            ; x (inl (inr (_ , inl vx))) → inr ⋆ , Q.f (fx x (inl vx))
            ; x (inl (inr (_ , inr vy))) → inr ⋆ , Q.f (fy x (inl vy))
            ; x (inr (inl (vx , vy))) → inl (Q.f (fx x (inr vx))) , Q.f (fy x (inr vy)) 
            ; x (inr (inr (_ , inl vx))) → inr ⋆ , Q.f (fx x (inr vx))
            ; x (inr (inr (_ , inr vy))) → inr ⋆ , Q.f (fy x (inr vy))
            })
 ∣P (inr _ , (py , y , (bay , bmy) , fy)) = py , ((inr ⋆) , (Q.f y)) , ((bay , bmy) , (λ x p → (inr ⋆) , (Q.f (fy x p))))


 ∣P-co : CoAlgebra
 E ∣P-co = (F Q.E + 𝟙) × F Q.E
 f ∣P-co = ∣P

 _∣ᶠ_ : Q.E → Q.E → Q.E
 a ∣ᶠ b = Q.uni ∣P-co .pr₁ .pr₁ ((inl (Q.f a)) , (Q.f b))

 &P : (F Q.E + 𝟙) × F Q.E → F ((F Q.E + 𝟙) × F Q.E)

 &P (inl (px , x , (bax , bmx) , fx) , (py , y , (bay , bmy) , fy))
   =   (px &ᵖ py)
     , ((inr ⋆) , (Q.f (exC> (((bax && bmy) , (bay && bmy)) , {!!}) ∣ᶠ (x ∣ᶠ y))))
     , {!!} , {!!}
 &P (inr _ , (py , y , (bay , bmy) , fy)) = py , ((inr ⋆) , (Q.f y)) , (bay , bmy) , (λ x p → (inr ⋆) , (Q.f y))




 
 -- {-# TERMINATING #-}
 -- _&ᶠ_ : (x y : F Q.E) → F Q.E
 -- _∣ᶠ_ : (x y : F Q.E) → F Q.E

 -- qx@(px , nx , excX@((bsaX , bsmX) , X)) &ᶠ qy@(py , ny , excY@((bsaY , bsmY) , Y))
 --   =   (px &ᵖ py)
 --     , (revQF ((Q.f nx ∣ᶠ Q.f ny) ∣ᶠ Q.f (exC-embed ((bsaX && bsmY , (bsaY && bsmX)) ,
 --       λ { x (inl (bsaX , bsmY)) → Q.f (X x (inl bsaX)) &ᶠ Q.f (Y x (inr bsmY))
 --       ; x (inr (bsaY , bsmX)) → Q.f (X x (inr bsmX)) &ᶠ Q.f (Y x (inl bsaY))})) )
 --     , (bsaX || bsaY , (bsmX || bsmY)) ,
 --       λ { x (inl (inl q)) → revQF (Q.f (X x (inl q)) &ᶠ qy) 
 --         ; x (inl (inr q)) → revQF (qx &ᶠ Q.f (Y x (inl q)))
 --         ; x (inr (inl q)) → revQF (Q.f (X x (inr q)) &ᶠ qy)
 --         ; x (inr (inr q)) → revQF (qx &ᶠ Q.f (Y x (inr q)))})

 -- qx ∣ᶠ qy
 --   = Q.f (exC-embed ((⊤B , ⊤B) , λ { x (inl q) → qx ; x (inr q) → qy}))
