{-# OPTIONS --safe --guardedness --without-K --exact-split #-}

open import MLTT.Spartan hiding (𝟚)
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc


-- This version tries to use coinductive records instead of a coalgebra.

module SType3 (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : _) (Msg : 𝓤 ̇) where

open PropositionalTruncation pt
open import BSet fe Msg
open import PSet fe pt Msg
open import CoAlgebra fe pt UA Msg


record SType : 𝓤 ⁺⁺ ̇  where
 coinductive
 field
  supPos : PSet
  inner : SType
  extern : ExC SType
  
open SType



st-CoAlgebra : CoAlgebra
CoAlgebra.E st-CoAlgebra = SType
CoAlgebra.f st-CoAlgebra x = supPos x , (inner x) , (extern x)


inv : PSet × SType × ExC SType → SType
supPos (inv (a , b , c)) = a
inner (inv (a , b , c)) = b
extern (inv (a , b , c)) = c

module _ where

 open CoAlgebra
 open CoAlgebra-morphism
      
 
 st-FCoAlgebra : Final-CoAlgebra
 Final-CoAlgebra.co st-FCoAlgebra = st-CoAlgebra
 Final-CoAlgebra.uni st-FCoAlgebra a = (d ∘ (f a) , co-morph refl) , q where
  d : F (E a) → SType
  supPos (d (ps , int , ex)) = ps
  inner (d (ps , int , ex)) = d (f a int)
  extern (d (ps , int , (ex1 , ex2))) = ex1 , (λ x x₁ → d (f a (ex2 x x₁)))

  q : is-central
       (Σ (coalg-morphism (Final-CoAlgebra.co st-FCoAlgebra) a))
       ((λ x → d (f a x)) , co-morph refl)
  q x = {!!}

 
-- module _ where
--  open embed st-FCoAlgebra


--  z : ExC SType → SType
--  ∣⟨ supPos (z ((bsa , bsm) , f)) ⟩ &ps = ∥ Σ x ꞉ Msg , Σ p ꞉ bsa x + bsm x , ∣⟨ supPos (f x p) ⟩ &ps ∥
--  ∣-is-prop (supPos (z ((bsa , bsm) , f))) &ps = ∥∥-is-prop
--  inner (z ((bsa , bsm) , f)) = z ((bsa , bsm) , (λ x p → inner (f x p)))
--  extern (z ((bsa , bsm) , f)) = e where
--   nbsa : BSet
--   nbsa mp =  Σ x ꞉ Msg , Σ p ꞉ bsa x + bsm x , pr₁ (pr₁ (extern (f x p))) mp
--   nbsm : BSet
--   nbsm mp =  Σ x ꞉ Msg , Σ p ꞉ bsa x + bsm x , pr₂ (pr₁ (extern (f x p))) mp
--   e : ExC SType
--   e = ((λ x → ∥ nbsa x ∥) , (λ x → ∥ nbsm x ∥)) , λ {x p → z {!!}}



--  _∣ᶠ_ : (x y : SType) → SType
--  qx ∣ᶠ qy = z ((⊤B , ⊤B) , λ { x (inl q) → qx ; x (inr q) → qy })


-- --  _&ᶠ_ : (x y : ExC SType) → SType
-- --  supPos (qx@((bsaX , bsmX) , X) &ᶠ qy@((bsaY , bsmY) , Y)) = supPos (z qx) &ᵖ supPos (z qy)
-- --  inner (px &ᶠ py) = (inner qx ∣ᶠ inner qy) ∣ᶠ ({!!} &ᶠ {!!}) where
-- --   qx = z px
-- --   qy = z py
-- --   excX = extern qx
-- --   excY = extern qy
-- --   bsX = pr₁ excX
-- --   bsaX = pr₁ bsX
-- --   bsmX = pr₂ bsX
-- --   X = pr₂ excX
-- --   bsY = pr₁ excY
-- --   bsaY = pr₁ bsY
-- --   bsmY = pr₂ bsY
-- --   Y = pr₂ excY
-- --  extern (((bsaX , bsmX) , X) &ᶠ ((bsaY , bsmY) , Y)) = {!!}
-- --

--  _&ᶠ_ : (x y : SType) → SType
--  supPos (qx &ᶠ qy) = supPos qx &ᵖ supPos qy
--  inner (qx &ᶠ qy) = (inner qx ∣ᶠ inner qy) ∣ᶠ ({!!} &ᶠ {!!}) where -- z ((bsaX && bsmY , (bsaY && bsmX)) ,
--  -- λ { x (inl (bsaX , bsmY)) → {!!} &ᶠ {!!}
--  --   ; x (inr (bsaY , bsmX)) → {!!} }) where
--   excX = extern qx
--   excY = extern qy
--   bsX = pr₁ excX
--   bsaX = pr₁ bsX
--   bsmX = pr₂ bsX
--   X = pr₂ excX
--   bsY = pr₁ excY
--   bsaY = pr₁ bsY
--   bsmY = pr₂ bsY
--   Y = pr₂ excY

--  extern (qx &ᶠ qy) = {!!}

