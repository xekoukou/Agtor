{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (rec)
open import MLTT.List
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import MLTT.Maybe
open import MLTT.Bool as B
open import MLTT.Vector

module Common where

_++v_ : ∀{m n} {X : 𝓤 ̇ } → Vector X m → Vector X n → Vector X (n +ℕ m)
[] ++v b = b
(x ∷ a) ++v b = x ∷ (a ++v b)

splitv : ∀ m n → {X : 𝓤 ̇ } → Vector X (n +ℕ m) → Vector X m × Vector X n
splitv zero n x = [] , x
splitv (succ m) n (x ∷ xs) = let (a , b) = splitv m n xs in (x ∷ a) , b

data ^ {𝓤} {𝓥} (A : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 _̂  : A → ^ {𝓤} {𝓥} A

dec→bool : ∀{𝓥} → {A : 𝓤 ̇ } → is-decidable A → ^ {𝓥} Bool
dec→bool (inl x) = true ̂
dec→bool (inr x) = false ̂
