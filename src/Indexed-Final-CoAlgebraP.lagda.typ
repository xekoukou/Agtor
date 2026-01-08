#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Final Coalgebra

#hide[
```agda

{-# OPTIONS --polarity --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Subsingletons

module Indexed-Final-CoAlgebraP where

open import Indexed-FunctorP
open import Indexed-CoAlgebraP
```
]

```agda
module _ {I : 𝓥 ̇ } where

 IFinal-CoAlgebra : IFunctor I 𝓤 → 𝓥 ⊔ 𝓤 ⁺ ̇
 IFinal-CoAlgebra func =
  Σ fc ꞉ ICoAlgebra func ,
   (∀ co → let open IMorphism func co fc in
                 Σ f ꞉ co-morphismᵢ func co fc , ((c : co-morphismᵢ func co fc) → f ↓ᵢ ＝ c ↓ᵢ ))
 module IFinal-CoAlgebra func (fc' : IFinal-CoAlgebra {𝓤 = 𝓤} func) where
 
  fcᵢ = fc' .pr₁
 
  uniᵢ : (∀ co → Σ f ꞉ co-morphismᵢ func co fcᵢ , ((c : co-morphismᵢ func co fcᵢ)
   → let open IMorphism func co fcᵢ in f ↓ᵢ ＝ c ↓ᵢ ))
  uniᵢ = fc' .pr₂

 module IFinal-CoAlgebra₁ {𝓤} func (fc' : IFinal-CoAlgebra {𝓤 = 𝓤} func) = IFinal-CoAlgebra func fc' renaming (fcᵢ to fcᵢ₁ ; uniᵢ to uniᵢ₁)
 module IFinal-CoAlgebra₂ {𝓤} func (fc' : IFinal-CoAlgebra {𝓤 = 𝓤} func) = IFinal-CoAlgebra func fc' renaming (fcᵢ to fcᵢ₂ ; uniᵢ to uniᵢ₂)
 module IFinal-CoAlgebra₃ {𝓤} func (fc' : IFinal-CoAlgebra {𝓤 = 𝓤} func) = IFinal-CoAlgebra func fc' renaming (fcᵢ to fcᵢ₃ ; uniᵢ to uniᵢ₃)
 module IFinal-CoAlgebra₄ {𝓤} func (fc' : IFinal-CoAlgebra {𝓤 = 𝓤} func) = IFinal-CoAlgebra func fc' renaming (fcᵢ to fcᵢ₄ ; uniᵢ to uniᵢ₄)
```

