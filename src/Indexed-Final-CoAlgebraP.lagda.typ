#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Final Coalgebra

#hide[
```agda

{-# OPTIONS --polarity --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Subsingletons

module Indexed-Final-CoAlgebraP (I : 𝓥 ̇ ) where

open import Indexed-FunctorP I
open import Indexed-CoAlgebraP I
```
]

```agda
IFinal-CoAlgebra : IFunctor 𝓤 → 𝓥 ⊔ 𝓤 ⁺ ̇
IFinal-CoAlgebra func =
 Σ fc ꞉ ICoAlgebra func ,
  (∀ co → let open ICoAlgebra₂ func co fc
              open IMorphism in
                Σ f ꞉ ico-morphism , ((c : ico-morphism) → f ↓ᵢ ＝ c ↓ᵢ ))
module IFinal-CoAlgebra func (fc' : IFinal-CoAlgebra {𝓤 = 𝓤} func) where

 fcᵢ = fc' .pr₁

 uniᵢ : (∀ co → let open ICoAlgebra₂ func co fcᵢ
                    open IMorphism in Σ f ꞉ ico-morphism , ((c : ico-morphism)
  → f ↓ᵢ ＝ c ↓ᵢ ))
 uniᵢ = fc' .pr₂
```

