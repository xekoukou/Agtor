{-# OPTIONS --cubical #-}

module DUniverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
import Cubical.Data.Bool as B
import Cubical.Data.List as L
-- open import Cubical.Data.String
import Cubical.Data.Unit as U
import Cubical.Data.Nat as N
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets

open import Cubical.Relation.Nullary

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
  ⋆Assoc (ProjC _ ctg) f g h = ΣPathP (refl , (funExt (λ x → ⋆Assoc ctg (snd f x) (snd g (fst f x)) (snd h (fst g (fst f x))))))
  isSetHom (ProjC _ ctg) {A} {B} = isSetΣ (isSetΠ (λ _ → is-set (snd B)))  λ f → isSetΠ (λ _ → isSetHom ctg)

DUMType : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
DUMType ℓ ℓ' = Proj ℓ (SET ℓ')

DUMTypeC : ∀ ℓ ℓ' → Category (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
DUMTypeC ℓ ℓ' = ProjC ℓ (SET ℓ')


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

