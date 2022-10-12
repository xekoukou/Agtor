{-# OPTIONS --cubical #-}

module Projection2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ where

  open Category

  record ProjStr (O : Category ℓ' ℓ'') (U : Type ℓ) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    constructor decidableprojstr
    inductive
    field
      ⟦_⟧ : U → ob O
      is-set : isSet U

  open ProjStr
  
  Proj : ∀ ℓ → Category ℓ' ℓ'' → Type (ℓ-max (ℓ-max ℓ' ℓ'') (ℓ-suc ℓ))
  Proj ℓ ctg = TypeWithStr ℓ (ProjStr ctg)

  ProjC : ∀ ℓ → (ctg : Category ℓ' ℓ'') → Category _ _
  ob (ProjC ℓ ctg) = Proj ℓ ctg
  Hom[_,_] (ProjC _ ctg) DA DB
    = Σ (⟨ DA ⟩ → ⟨ DB ⟩) λ f → ∀ x → Hom[_,_] ctg (⟦_⟧ (snd DA) x) (⟦_⟧ (snd DB) (f x))
  id (ProjC _ ctg) = (λ x → x) , (λ _ → id ctg)
  _⋆_ (ProjC _ ctg) f g
    = let q = (λ x → (fst g) ((fst f) x))
      in q , λ x → _⋆_ ctg ((snd f) x) ((snd g) (fst f x))
  ⋆IdL (ProjC _ ctg) f = ΣPathP (refl , funExt (λ x → ⋆IdL ctg (snd f x)))
  ⋆IdR (ProjC _ ctg) f = ΣPathP (refl , funExt (λ x → ⋆IdR ctg (snd f x)))
  ⋆Assoc (ProjC _ ctg) f g h
    = ΣPathP (refl , (funExt (λ x → ⋆Assoc ctg (snd f x) (snd g (fst f x)) (snd h (fst g (fst f x))))))
  isSetHom (ProjC _ ctg) {A} {B} = isSetΣ (isSetΠ (λ _ → is-set (snd B)))  λ f → isSetΠ (λ _ → isSetHom ctg)


-- postulate
--   UAType : Type₁
--   DUAType : DecUniverse UAType ActorT

-- -- infix 1000 #_

-- -- mutual

-- --   data UType : Type₁ where
-- --     #_     : StT   → UType

-- --   data StT : Type₁ where
-- --     _×_   : UType → UType → StT 
-- --     List  : UType → StT
-- --     Unit  : StT 
-- --     Bool  : StT
-- --     ℕ     : StT


-- -- ⟨_⟩   : UType → Set
-- -- ⟨ # Unit ⟩ = U.Unit
-- -- ⟨ # Bool ⟩ = B.Bool
-- -- ⟨ # ℕ ⟩ = N.ℕ
-- -- ⟨ # (A × B) ⟩  = ⟨ A ⟩ S.× ⟨ B ⟩
-- -- ⟨ # (List A) ⟩  = L.List ⟨ A ⟩



-- module _ where

--   open DecidableStr
--   open Functor

--   FS : Functor (DecidableC ℓ ℓ') (SET ℓ')
--   F-ob FS = {!!}
--   F-hom FS = {!!}
--   F-id FS = {!!}
--   F-seq FS = {!!}

