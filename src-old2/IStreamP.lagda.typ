
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Indexed-Stream

-- TODO Remove this as unnessary.
/*
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split #-}

open import MLTT.Spartan

```
*/

```agda

module IStreamP {𝓦 𝓠} (A : 𝓦 ̇ ) (B : A → 𝓠 ̇ ) (nextₛ : A → A) where
 open import Indexed-FunctorP A
 open import Indexed-Final-CoAlgebraP A
 open import Indexed-CoAlgebraP A

 FIStream : IFunctor 𝓠
 FIStream =
     (λ X i → B i × X (nextₛ i))
   , (λ f i x → (x .pr₁) , (f (nextₛ i) (x .pr₂)))
   , (λ f g → refl)
   , λ {X} → refl

 IStream : 𝓦 ⊔ 𝓠 ⁺ ̇
 IStream = IFinal-CoAlgebra FIStream


 open IFunctor FIStream
 open ICoAlgebra FIStream
 
 module IStream (fc' : IStream) where
 
  open IFinal-CoAlgebra FIStream fc'
 
  next : ∀{b} → Fnᵢ ⟨ fcᵢ ⟩ b → ⟨ fcᵢ ⟩ (nextₛ b)
  next a = a .pr₂
 
  value : ∀{b} → Fnᵢ ⟨ fcᵢ ⟩ b → B b
  value a = a .pr₁

  nextℕ : A → ℕ → A
  nextℕ a zero = a
  nextℕ a (succ n) = nextℕ (nextₛ a) n

  _atᵢ_ : ∀{b} → Fnᵢ ⟨ fcᵢ ⟩ b → (k : ℕ) → Fnᵢ ⟨ fcᵢ ⟩ (nextℕ b k)
  d atᵢ zero = d
  (a , d) atᵢ (succ n) = ((fcᵢ ⟶ᵢ) (nextₛ _) d) atᵢ n
