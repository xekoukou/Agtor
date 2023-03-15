{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Empty
open import Cubical.Data.Maybe
open import Cubical.Data.Sum
open import Cubical.Data.Fin
open import Cubical.Data.Vec as V
open import Cubical.Data.List
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Core.Id hiding (_≡_)

module Common where

_==?_ : (x y : ℕ) → Dec (Id x y)
zero ==? zero = yes reflId
zero ==? suc y = no λ {()}
suc x ==? zero = no λ {()}
suc x ==? suc y with x ==? y
... | yes reflId = yes reflId
... | no ¬p = no (λ { reflId → ¬p reflId})


-- TODO Chech Data.List.Dependent
data HList {ℓ} : List (Type ℓ) → Type (ℓ-suc ℓ) where
  []ₕ : HList []
  _∷ₕ_ : {A : Type ℓ} {AS : List (Type ℓ)} → A → HList AS → HList (A ∷ AS)


data _∈_ {ℓ : Level} {A : Type ℓ} (x : A) : List A → Type ℓ where
  here : ∀{xs} → x ∈ (x ∷ xs)
  there : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)


 -- All old Secrets should be known to the actor.
 -- first argument is the secrets of the msg
 -- returns the position of the secret to the actor list of secrets.
compSecr : ∀{fv k1 k2} → Vec (Fin fv) k1 → Vec (Fin fv) k2 → Maybe (List (Fin k2))
compSecr [] ys = just []
compSecr (x ∷ xs) ys = (compS x ys) >>=M λ x → compSecr xs ys >>=M λ ys → just (x ∷ ys) where
  compS : ∀ {fv} {k2} (x : Fin fv) (ys : Vec (Fin fv) k2) → Maybe (Fin k2)
  compS x [] = nothing
  compS x (y ∷ ys) with fst x =? fst y
  ... | yes p = just fzero
  ... | no ¬p = compS x ys >>=M λ x → just (fsuc x)

