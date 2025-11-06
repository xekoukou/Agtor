#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Final Coalgebra

#hide[
```agda

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Subsingletons

module Final-CoAlgebraP  where

open import FunctorP
open import CoAlgebraP
```
]

```agda
Final-CoAlgebra : Functor 𝓤 → 𝓤 ⁺ ̇
Final-CoAlgebra func = Σ fc ꞉ CoAlgebra func , (∀ co → let open CoAlgebra₂ func co fc in is-singleton co-morphism)

module Final-CoAlgebra func (fc' : Final-CoAlgebra {𝓤 = 𝓤} func) where

 fc = fc' .pr₁

 uni : (∀ co → let open CoAlgebra₂ func co fc in is-singleton co-morphism)
 uni = fc' .pr₂
```

