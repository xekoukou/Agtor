{-# OPTIONS --cubical #-}

module ProductCommMonoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.CommMonoid
open import Cubical.Data.Sigma

module _ {ℓ ℓ'} (CMA : CommMonoid ℓ) (CMB : CommMonoid ℓ') where

  private
    
    A = ⟨ CMA ⟩
    B = ⟨ CMB ⟩
  
    P = A × B
    
    module Q = CommMonoidStr (snd CMA)
    module R = CommMonoidStr (snd CMB)
    module QI = IsCommMonoid Q.isCommMonoid
    module RI = IsCommMonoid R.isCommMonoid
  
    _*_ : P → P → P
    _*_ (x1 , y1) (x2 , y2) = (x1 Q.· x2) , (y1 R.· y2)
    
    p-isSet : isSet P
    p-isSet = isSetΣ (QI.is-set) λ _ → RI.is-set
    
    assoc* : (x y z : P) →
             (x * (y * z)) ≡ ((x * y) * z)
    assoc* (x1 , x2) (y1 , y2) (z1 , z2) = λ i → (QI.assoc x1 y1 z1 i) , (RI.assoc x2 y2 z2 i)
    
    rid* : (x : P) →
           (x * (Q.ε , R.ε)) ≡ x
    rid* (x1 , x2) i = (QI.rid x1 i) , (RI.rid x2 i)
    
    lid* : (x : P) →
           ((Q.ε , R.ε) * x) ≡ x
    lid* (x1 , x2) i = ((QI.comm _ x1 ∙ Q.rid x1) i) , (((R.comm _ x2 ∙ R.rid x2) i))
    
    comm* : (x y : P) →
              (x * y) ≡ (y * x)
    comm* (x1 , x2) (y1 , y2) = λ i → (Q.comm x1 y1 i) , (R.comm x2 y2 i)

  ProductCommMonoid : CommMonoid _
  ProductCommMonoid = makeCommMonoid (Q.ε , R.ε) _*_ p-isSet assoc* rid* comm*

