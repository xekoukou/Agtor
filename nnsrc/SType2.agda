{-# OPTIONS --safe --guardedness --without-K --exact-split #-}

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

-- This version tries to use coinductive records instead of a coalgebra.

module SType2 (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) where

open PropositionalTruncation pt
open import BSet2 Msg


record &PSet : 𝓤 ⁺ ̇  where
 field
  &⟨_⟩ : (o : 𝟚 × BSet) → 𝓤 ̇ 
  &-is-prop : ∀ o → is-prop (&⟨_⟩ o)


_ᵗ : 𝟚 × BSet → 𝟚 × BSet
(𝕞 , x) ᵗ = 𝕒 , x
(𝕒 , x) ᵗ = 𝕞 , x

-- This predicate describes all the possible superpositions of a system.
record PSet : 𝓤 ⁺⁺ ̇  where
 field
  ∣⟨_⟩ : (o : &PSet) → 𝓤 ⁺ ̇ 
  ∣-is-prop : ∀ o → is-prop (∣⟨_⟩ o)

open &PSet public
open PSet public


_&-&ᵖ_ : &PSet → &PSet → &PSet
&⟨ A &-&ᵖ B ⟩ o = ∥ &⟨ A ⟩ o + &⟨ B ⟩ o ∥
&-is-prop (A &-&ᵖ B) o = ∥∥-is-prop

_&ᵖ_ : PSet → PSet → PSet
∣⟨ A &ᵖ B ⟩ o = ∥ Σ &A ꞉ &PSet , Σ &B ꞉ &PSet , ∣⟨ A ⟩ &A × ∣⟨ B ⟩ &B × (&A &-&ᵖ &B ＝ o)  ∥
((A &ᵖ B) .∣-is-prop) o = ∥∥-is-prop

_∣ᵖ_ : PSet → PSet → PSet
∣⟨ A ∣ᵖ B ⟩ o = ∥ ∣⟨ A ⟩ o + ∣⟨ B ⟩ o ∥
∣-is-prop (A ∣ᵖ B) o = ∥∥-is-prop


ExC : 𝓤 ⁺⁺ ̇  → 𝓤 ⁺⁺ ̇
ExC X = ( Σ B ꞉ BSet × BSet , (∀ x → B .pr₁ x + B .pr₂ x → X))

record SType : 𝓤 ⁺⁺ ̇  where
 coinductive
 field
  supPos : PSet
  inner : SType
  extern : ExC SType
  
open SType

-- We define the coalgebra of a functor F

-- We may need to add all the secrets here as well, for every part of the type and state to use it.
-- both the PSet and the two types.

-- This is a functor
F : 𝓤 ⁺⁺ ̇  → 𝓤 ⁺⁺ ̇
F X = PSet × X × ExC X

Fm : ∀{X Y} → (f : X → Y) → F X → F Y
Fm f (p , x , (bset , g)) = p , f x , bset , (λ x bs → f (g x bs))


-- CoAlgebra

record CoAlgebra : 𝓤 ⁺⁺ ⁺ ̇  where
 field
  E : 𝓤 ⁺⁺ ̇
  f : E → F E


st-CoAlgebra : CoAlgebra
CoAlgebra.E st-CoAlgebra = SType
CoAlgebra.f st-CoAlgebra x = supPos x , (inner x) , (extern x)


inv : PSet × SType × ExC SType → SType
supPos (inv (a , b , c)) = a
inner (inv (a , b , c)) = b
extern (inv (a , b , c)) = c

module CoAlgebra-morphism (b a : CoAlgebra) where
 module A = CoAlgebra a
 module B = CoAlgebra b

 record coalg-morphism (f : A.E → B.E) : 𝓤 ⁺⁺ ̇  where
  constructor co-morph 
  field
   di-comm : Fm f ∘ A.f ＝ B.f ∘ f


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
  q = {!!}

-- According to theorem 2.1 
-- https://ncatlab.org/nlab/show/terminal+coalgebra+for+an+endofunctor
-- F X is is isomorphic to X if X is a final coalgebra
-- TODO Check that this category is univalent and thus isomorphism leads to equalityz
-- The way we defined it , it is univalent, we are in the category of Sets and
-- we have the univalence theorem

module embed (fc : Final-CoAlgebra) where
 module Q = Final-CoAlgebra fc

 -- postulate
 -- Make sure this is a unique homeomorphism, or that it does not interfere in any way..
 -- Due to uniqueness of the coalgebra morphism of the terminal object
 -- there is a unique isomophism.
 -- Any isomophism creates a coalgebraic morphism.
 -- eqFQ : Q.E ＝ F Q.E
 -- revQF : F Q.E → Q.E
-- Q.f is the one direction of this unique isomorphism


 w : ExC (F Q.E) → F (ExC (F Q.E))
 ∣⟨ pr₁ (w ((bsa , bsm) , f)) ⟩ &ps = ∥ Σ x ꞉ Msg , Σ p ꞉ bsa x + bsm x , ∣⟨ pr₁ (f x p) ⟩ &ps ∥
 ∣-is-prop (pr₁ (w e)) &ps = ∥∥-is-prop
 pr₂ (w ((bsa , bsm) , f)) = ((bsa  , bsm) , (λ x p → Q.f (pr₁ (pr₂ (f x p))))) , e where
  nbsa : BSet
  nbsa mp =  Σ x ꞉ Msg , Σ p ꞉ bsa x + bsm x ,   pr₁ (pr₁ (pr₂ (pr₂ (f x p)))) mp
  nbsm : BSet
  nbsm mp =  Σ x ꞉ Msg , Σ p ꞉ bsa x + bsm x ,   pr₂ (pr₁ (pr₂ (pr₂ (f x p)))) mp
  -- The way we construct e may have been simpler.... we only care about nbsa and nbsm, not about the function they return having the correct structure, left for actors, right for messages.
  -- it works for now.
  e : ExC (ExC (F Q.E))
  e = ((λ x → ∥ nbsa x ∥) , (λ x → ∥ nbsm x ∥)) ,
    λ { x (inl _) →
      ((λ y → Σ p ꞉ bsa y ,   pr₁ (pr₁ (pr₂ (pr₂ (f y (inl p))))) x) , (λ y → Σ p ꞉ bsm y ,   pr₁ (pr₁ (pr₂ (pr₂ (f y (inr p))))) x))
        , λ { y (inl (p , t)) → Q.f ((pr₂ (pr₂ (pr₂ (f y (inl p))))) x (inl t))
            ; y (inr (p , t)) → Q.f ((pr₂ (pr₂ (pr₂ (f y (inr p))))) x (inl t))}
      ; x (inr _) →
      ((λ y → Σ p ꞉ bsa y ,   pr₂ (pr₁ (pr₂ (pr₂ (f y (inl p))))) x) , (λ y → Σ p ꞉ bsm y ,   pr₂ (pr₁ (pr₂ (pr₂ (f y (inr p))))) x))
        , λ { y (inl (p , t)) → Q.f ((pr₂ (pr₂ (pr₂ (f y (inl p))))) x (inr t))
            ; y (inr (p , t)) → Q.f ((pr₂ (pr₂ (pr₂ (f y (inr p))))) x (inr t))}}


 coExC : CoAlgebra
 CoAlgebra.E coExC = ExC (F Q.E)
 CoAlgebra.f coExC = w

-- Since Q is a terminal object, we have a coalgebraic morphism that embeds coExC into Q.

 exC-morph : _
 exC-morph = Q.uni coExC
 exC-embed = pr₁ (pr₁ exC-morph)

 
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

module _ where
 open embed st-FCoAlgebra


 z : ExC SType → SType
 ∣⟨ supPos (z ((bsa , bsm) , f)) ⟩ &ps = ∥ Σ x ꞉ Msg , Σ p ꞉ bsa x + bsm x , ∣⟨ supPos (f x p) ⟩ &ps ∥
 ∣-is-prop (supPos (z ((bsa , bsm) , f))) &ps = ∥∥-is-prop
 inner (z ((bsa , bsm) , f)) = z ((bsa , bsm) , (λ x p → inner (f x p)))
 extern (z ((bsa , bsm) , f)) = e where
  nbsa : BSet
  nbsa mp =  Σ x ꞉ Msg , Σ p ꞉ bsa x + bsm x , pr₁ (pr₁ (extern (f x p))) mp
  nbsm : BSet
  nbsm mp =  Σ x ꞉ Msg , Σ p ꞉ bsa x + bsm x , pr₂ (pr₁ (extern (f x p))) mp
  e : ExC SType
  e = ((λ x → ∥ nbsa x ∥) , (λ x → ∥ nbsm x ∥)) , λ {x p → z {!!}}



 _∣ᶠ_ : (x y : SType) → SType
 qx ∣ᶠ qy = z ((⊤B , ⊤B) , λ { x (inl q) → qx ; x (inr q) → qy })


--  _&ᶠ_ : (x y : ExC SType) → SType
--  supPos (qx@((bsaX , bsmX) , X) &ᶠ qy@((bsaY , bsmY) , Y)) = supPos (z qx) &ᵖ supPos (z qy)
--  inner (px &ᶠ py) = (inner qx ∣ᶠ inner qy) ∣ᶠ ({!!} &ᶠ {!!}) where
--   qx = z px
--   qy = z py
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
--  extern (((bsaX , bsmX) , X) &ᶠ ((bsaY , bsmY) , Y)) = {!!}
--

 _&ᶠ_ : (x y : SType) → SType
 supPos (qx &ᶠ qy) = supPos qx &ᵖ supPos qy
 inner (qx &ᶠ qy) = (inner qx ∣ᶠ inner qy) ∣ᶠ ({!!} &ᶠ {!!}) where -- z ((bsaX && bsmY , (bsaY && bsmX)) ,
 -- λ { x (inl (bsaX , bsmY)) → {!!} &ᶠ {!!}
 --   ; x (inr (bsaY , bsmX)) → {!!} }) where
  excX = extern qx
  excY = extern qy
  bsX = pr₁ excX
  bsaX = pr₁ bsX
  bsmX = pr₂ bsX
  X = pr₂ excX
  bsY = pr₁ excY
  bsaY = pr₁ bsY
  bsmY = pr₂ bsY
  Y = pr₂ excY

 extern (qx &ᶠ qy) = {!!}

