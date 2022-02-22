{-# OPTIONS --cubical #-}

module UType where

open import Cubical.Foundations.Prelude
import Cubical.Data.Bool as B
import Cubical.Data.List as L
-- open import Cubical.Data.String
import Cubical.Data.Unit as U
import Cubical.Data.Nat as N
import Cubical.Data.Sigma as S
open import Cubical.Data.Maybe

open import Cubical.Relation.Nullary

variable
  ℓ ℓ' : Level


data Tree (A : Type ℓ) : Type ℓ where
  ε    : Tree A
  `_   : A → Tree A
  _·_  : Tree A → Tree A → Tree A



record DecUniverse (U : Type ℓ) (V : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  inductive
  field
    ⟦_⟧ : U → V
    dec : Discrete U



postulate
  UMType : Type₁
  DUMType : DecUniverse UMType Type


record ActorT : Type₁ where
  coinductive

  open DecUniverse DUMType
  field
    P : UMType → Type
    decP  : ∀ A → Maybe (P A)
    image : ∀ {A} → { p : P A } → ⟦ A ⟧ → Tree UMType
    next  : ∀ {A} → { p : P A } → ⟦ A ⟧ → Tree ActorT

postulate
  UAType : Type₁
  DUAType : DecUniverse UAType ActorT

-- infix 1000 #_

-- mutual

--   data UType : Type₁ where
--     #_     : StT   → UType

--   data StT : Type₁ where
--     _×_   : UType → UType → StT 
--     List  : UType → StT
--     Unit  : StT 
--     Bool  : StT
--     ℕ     : StT


-- ⟨_⟩   : UType → Set
-- ⟨ # Unit ⟩ = U.Unit
-- ⟨ # Bool ⟩ = B.Bool
-- ⟨ # ℕ ⟩ = N.ℕ
-- ⟨ # (A × B) ⟩  = ⟨ A ⟩ S.× ⟨ B ⟩
-- ⟨ # (List A) ⟩  = L.List ⟨ A ⟩
