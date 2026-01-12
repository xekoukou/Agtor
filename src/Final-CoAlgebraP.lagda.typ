#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Final Coalgebra

#hide[
```agda

{-# OPTIONS --polarity --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Subsingletons

module Final-CoAlgebraP  where

open import FunctorP
open import CoAlgebraP
```
]

```agda
Final-CoAlgebra : Functor 𝓤 → 𝓤 ⁺ ̇
Final-CoAlgebra func =
 Σ fc ꞉ CoAlgebra func ,
  (∀ co → let open CoAlgebra₂ func co fc
              open Morphism in
                Σ f ꞉ co-morphism , ((c : co-morphism) → f ↓ ＝ c ↓ ))
module Final-CoAlgebra func (fc' : Final-CoAlgebra {𝓤 = 𝓤} func) where

 fc = fc' .pr₁

 uni : (∀ co → let open CoAlgebra₂ func co fc
                   open Morphism in Σ f ꞉ co-morphism , ((c : co-morphism)
  → f ↓ ＝ c ↓ ))
 uni = fc' .pr₂


module Final-CoAlgebra₁ {𝓤} func (fc' : Final-CoAlgebra {𝓤 = 𝓤} func) = Final-CoAlgebra func fc' renaming (fc to fc₁ ; uni to uni₁)
```

