#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Common functions for the realization


/*

```agda
{-# OPTIONS --without-K --exact-split --cubical --guardedness #-}

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.Base
open import UF.FunExt
import Cubical.Foundations.Prelude as Cube

```

*/

```agda

module Common-Rel where

eqToPath : {A : 𝓤 ̇ } → {x y : A} → x ＝ y → Cube.Path A x y
eqToPath refl = Cube.refl

pathToEq : {A : 𝓤 ̇ } → {x y : A} → Cube.Path A x y → x ＝ y
pathToEq {x = x} = Cube.J (λ y _ → x ＝ y) refl

pathToEq-reflPath : {A : 𝓤 ̇ } → {x y : A} → (pathToEq Cube.refl) ＝ refl {x = x}
pathToEq-reflPath {x = x} = pathToEq (Cube.JRefl (λ y _ → x ＝ y) refl)


substPath≡transport' : {A : 𝓥 ̇  } → (C : A → 𝓤 ̇ ) → {x y : A} → (b : C x) → (p : x ＝ y) → Cube.subst C (eqToPath p) b Cube.≡ transport C p b
substPath≡transport' C b refl = Cube.transportRefl b


dfunextCube : DN-funext 𝓤 𝓥
dfunextCube f~g = pathToEq λ i x → eqToPath (f~g x) i


```
