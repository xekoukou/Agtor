open import MLTT.Spartan hiding (rec)
open import MLTT.List
open import MLTT.Maybe
open import MLTT.Vector
open import UF.Subsingletons
open import Naturals.Order
open import UF.FunExt
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Notation.General
open import UF.Sets
open import UF.Base
open import UF.Univalence
open import UF.Embeddings
open import Categories.Functor

module F-Coalgebra (fe : Fun-Ext) (UA : Univalence) where

⟨_⟩ : hSet 𝓤 → 𝓤 ̇
⟨ hS ⟩ = pr₁ hS

open import Categories.Category fe

cat : ∀{𝓤 𝓥} → category {!!} {!!}
pr₁ (precategory.str (pr₁ (cat {𝓤} {𝓥}))) = hSet 𝓤
pr₁ (pr₂ (precategory.str (pr₁ (cat {𝓤} {𝓥})))) A B = ⟨ A ⟩ → ⟨ B ⟩
pr₁ (pr₂ (pr₂ (precategory.str (pr₁ (cat {𝓤} {𝓥}))))) A = λ x → x
pr₂ (pr₂ (pr₂ (precategory.str (pr₁ (cat {𝓤} {𝓥}))))) A B C f g x = g (f x)
pr₁ (precategory.ax (pr₁ (cat {𝓤} {𝓥}))) A B p q = {!!} -- Π-is-set fe (λ _ → pr₂ B) p q
pr₁ (pr₂ (precategory.ax (pr₁ (cat {𝓤} {𝓥})))) = λ A B f → refl
pr₁ (pr₂ (pr₂ (precategory.ax (pr₁ (cat {𝓤} {𝓥}))))) A B f = refl
pr₂ (pr₂ (pr₂ (precategory.ax (pr₁ (cat {𝓤} {𝓥}))))) A B C D f g h = refl
pr₂ (cat {𝓤} {𝓥}) A B = {!!}
