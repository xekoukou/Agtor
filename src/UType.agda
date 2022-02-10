{-# OPTIONS --cubical #-}

module UType where

open import Cubical.Foundations.Prelude
import Cubical.Data.Bool as B
import Cubical.Data.List as L
-- open import Cubical.Data.String
import Cubical.Data.Unit as U
import Cubical.Data.Nat as N
import Cubical.Data.Sigma as S


infix 1000 #_

mutual

  data UType : Type₁ where
    #_     : StT   → UType

  data StT : Type₁ where
    _×_   : UType → UType → StT 
    List  : UType → StT
    Unit  : StT 
    Bool  : StT
    ℕ     : StT


⟨_⟩   : UType → Set
⟨ # Unit ⟩ = U.Unit
⟨ # Bool ⟩ = B.Bool
⟨ # ℕ ⟩ = N.ℕ
⟨ # (A × B) ⟩  = ⟨ A ⟩ S.× ⟨ B ⟩
⟨ # (List A) ⟩  = L.List ⟨ A ⟩
