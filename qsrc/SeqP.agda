{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

module SeqP (Msg : 𝓤 ̇ ) 𝓥 Cm 𝓦 Cp where

 open import FCP {𝓦 = 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺} Msg 𝓥 Cm

 open import PredP 
 BSet = ΣPred Msg 𝓥 Cm

 &PSet = ΣPred BSet 𝓦 Cp 

 open import FunctorP
 open import Final-CoAlgebraP

 Fseq : Functor (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺)
 Fseq =
    (λ X → X × &PSet × FC X)
  , (λ f (x , &ps , ((mp , fm) , (ap , fa))) → f x , &ps , (mp , λ x c → f (fm x c)) , (ap , λ x c → f (fa x c)))
  , (λ f g x → refl)
  , λ x → refl

 Seq = Final-CoAlgebra Fseq
