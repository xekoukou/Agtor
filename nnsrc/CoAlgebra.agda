{-# OPTIONS --safe --without-K --exact-split #-}


open import UF.FunExt

module CoAlgebra (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties
open import UF.Equiv
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import UF.Subsingletons-FunExt
open import UF.Equiv-FunExt

open import Categories.Category fe
open import Categories.Functor fe

module _ {𝓤 𝓥} (c : precategory 𝓤 𝓥) where

 open functor-of-precategories c c

 private
  module C = precategory c

 module _ (fct : functor) where
  private
   module F = functor fct

 
  coalgebra : 𝓤 ⊔ 𝓥 ̇
  coalgebra = Σ E ꞉ C.ob , C.hom E (F.ob E)

  module Coalgebra (c : coalgebra) where
   E : C.ob
   E = pr₁ c

   f : C.hom E (F.ob E)
   f = pr₂ c

  module Coalgebra-morphism (a b : coalgebra) where
   private
    module A = Coalgebra a
    module B = Coalgebra b

   dia-comm : (f : C.hom A.E B.E) → 𝓥 ̇
   dia-comm f = C.cmp (F.hom f) A.f ＝ C.cmp B.f f

  open Coalgebra-morphism public
  open Coalgebra
  
  F-Coalgebra-category-structure : category-structure (𝓤 ⊔ 𝓥) 𝓥
  pr₁ (F-Coalgebra-category-structure) = coalgebra
  pr₁ (pr₂ F-Coalgebra-category-structure) a b = Σ (dia-comm a b)
  pr₁ (pr₂ (pr₂ F-Coalgebra-category-structure)) A
   = (C.idn (E A)) , (ap (λ z → C.cmp z (f A)) (F.preserves-idn (E A)) ∙ (C.idn-R _ _ _ ∙ C.idn-L _ _ _ ⁻¹))
  pr₁ (pr₂ (pr₂ (pr₂ F-Coalgebra-category-structure)) A B C d g) = C.cmp (pr₁ g) (pr₁ d)
  pr₂ (pr₂ (pr₂ (pr₂ F-Coalgebra-category-structure)) A B C d g) = (ap (λ z → C.cmp z (f A)) (F.preserves-seq _ _ _ _ _) ∙ (C.assoc _ _ _ _ _ _ _ ∙ (ap (λ z → C.cmp (F.hom (pr₁ g)) z) (pr₂ d) ∙ (C.assoc _ _ _ _ _ _ _ ⁻¹ ∙ (ap (λ z → C.cmp z (pr₁ d)) (pr₂ g) ∙ C.assoc _ _ _ _ _ _ _)))))
  
  F-Coalgebra-precategory-axioms : precategory-axioms (F-Coalgebra-category-structure)
  pr₁ F-Coalgebra-precategory-axioms A B z= d=
   = Σ-is-set (C.hom-is-set _ _) (λ _ → props-are-sets (C.hom-is-set _ _)) z= d=
  pr₁ (pr₂ F-Coalgebra-precategory-axioms) A B d = to-Σ-＝ (C.idn-L _ _ _ , (C.hom-is-set _ _ _ _))
  pr₁ (pr₂ (pr₂ F-Coalgebra-precategory-axioms)) A B d = to-Σ-＝ (C.idn-R _ _ _ , (C.hom-is-set _ _ _ _))
  pr₂ (pr₂ (pr₂ F-Coalgebra-precategory-axioms)) A B C D d g h = to-Σ-＝ ((C.assoc _ _ _ _ _ _ _) , (C.hom-is-set _ _ _ _))
  
  F-Coalgebra-precategory : precategory (𝓤 ⊔ 𝓥) 𝓥
  F-Coalgebra-precategory = make (F-Coalgebra-category-structure) F-Coalgebra-precategory-axioms

-- Is this true?
--   F-Coalgebra-category : category (𝓤 ⊔ 𝓥) 𝓥
--   pr₁ F-Coalgebra-category = F-Coalgebra-precategory 
--   pr₂ F-Coalgebra-category A B = hs , {!!} where
--    hs : has-section (＝-to-iso F-Coalgebra-precategory A B)
--    hs = (λ { (d , e , lid , rid) → {!!}}) , {!!}
   
