{-# OPTIONS --guardedness --without-K --exact-split #-}

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

module CoAlgebra-Rel (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence)
                  (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) {𝓥} {𝓦} {𝓣} where


open PropositionalTruncation pt
open import UF.ImageAndSurjection pt

open import xBSet fe pt Msg Secret
open import &PSet (𝟚 × ×BSet 𝓥) pt
open import PSet pt (&PSet 𝓦 × &PSet 𝓦) 
open import Scope fe pt Msg Secret

open import CoAlgebra fe pt UA Msg Secret  {𝓥} {𝓦} {𝓣}

record CoT : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇  where
 coinductive
 field
  supPos : PSet 𝓣
  inner : CoT
  extern : ExC CoT
  
open CoT

record CoTEq (a b : CoT) : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇  where
 coinductive
 field
  psEq : supPos a ＝ supPos b
  inEq : CoTEq (inner a) (inner b)
  extEq : Σ ×BsEq ꞉ pr₁ (extern a) ＝ pr₁ (extern b) , (∀ x p → CoTEq (pr₂ (extern a) x p) (pr₂ (extern b) x (transport (λ z → ⟨ z .pr₁ .pr₁ ⟩ x + ⟨ z .pr₂ .pr₁ ⟩ x) ×BsEq p))) 

open CoTEq

coTEq-refl : ∀{ a} → CoTEq a a
psEq (coTEq-refl {a}) = refl
inEq (coTEq-refl {a}) = coTEq-refl
extEq (coTEq-refl {a}) = refl , λ x p → coTEq-refl



module _ (coTEq→eq : ∀{ a b} → CoTEq a b → a ＝ b) where

  
  -- TODO CoT is a Set ?!?!?
  
  coAlgebra-rel : CoAlgebra
  coAlgebra-rel = CoT , λ x → supPos x , (inner x) , (extern x)
  
  
  inv : PSet 𝓣 × CoT × ExC CoT → CoT
  supPos (inv (a , b , c)) = a
  inner (inv (a , b , c)) = b
  extern (inv (a , b , c)) = c
  
  module _ where
   open CoAlgebra coAlgebra-rel
  
   inv-f-iso : f ∘ inv ＝ (λ x → x)
   inv-f-iso = dfunext fe (λ x → refl)
  
   f-inv-iso : inv ∘ f ＝ (λ x → x)
   f-inv-iso = dfunext fe (λ x → coTEq→eq (r x)) where
    r : ∀ x → CoTEq _ _
    psEq (r x) = refl
    inEq (r x) = coTEq-refl
    extEq (r x) = refl , (λ mp p → coTEq-refl)
  
  module _ where

   open CoAlgebra
   open Final-CoAlgebra-universal coAlgebra-rel

   private
    module FC = CoAlgebra coAlgebra-rel
   
     
   st-FCoAlgebra : Final-CoAlgebra
   st-FCoAlgebra = coAlgebra-rel , l1  where
    l1 : uniT
    l1 a = (d ∘ (f a) , refl) , q where
      d : F (E a) → CoT
      supPos (d (ps , int , ex)) = ps
      inner (d (ps , int , ex)) = d (f a int)
      extern (d (ps , int , (ex1 , ex2))) = ex1 , (λ x x₁ → d (f a (ex2 x x₁))) 
    
      q : (b : coalg-morphism a coAlgebra-rel) →
           (λ x → d (f a x)) ＝ pr₁ b
           
      q (t , eq) = ap (λ z → λ x → z (f a x)) e ∙ ap (inv ∘_) eq ∙ ap (_∘ t) f-inv-iso where
       e : d ＝ inv ∘ Fm t
       e = dfunext fe (λ x → (coTEq→eq {a = d x} {b = (inv ∘ Fm t) x}) (s x)) where
        s : (x : F (E a)) → CoTEq (d x) (inv ((Fm t) x))
        psEq (s (p , ix , ex)) = refl
        inEq (s (p , ix , ex)) with (t ix) | ap (λ z → z ix) ((ap (inv ∘_) eq ∙ ap (_∘ t) f-inv-iso))
        ... | _ | refl = s (f a ix)
        pr₁ (extEq (s (p , ix , ex))) = refl
        pr₂ (extEq (s (p , ix , ex))) x v with (t (pr₂ ex x v)) | ap (λ z → z ((pr₂ ex x v))) ((ap (inv ∘_) eq ∙ ap (_∘ t) f-inv-iso))
        ... | _ | refl = s (f a (pr₂ ex x v))
