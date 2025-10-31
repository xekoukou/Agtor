{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Subsingletons

module Final-CoAlgebraP  where

open import FunctorP
open import CoAlgebraP

Final-CoAlgebra : Functor 𝓤 → 𝓤 ⁺ ̇
Final-CoAlgebra func = Σ fc ꞉ CoAlgebra func , (∀ co → let open CoAlgebra₂ func co fc in is-singleton f-co-morphism)

module Final-CoAlgebra func (fc' : Final-CoAlgebra {𝓤 = 𝓤} func) where

 fc = fc' .pr₁

 open CoAlgebra func fc public

 uni : (∀ co → let open CoAlgebra₂ func co fc in is-singleton f-co-morphism)
 uni = fc' .pr₂


