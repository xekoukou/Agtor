{-# OPTIONS  --confluence-check --sized-types --cubical #-}

module SemiRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Algebra.CommMonoid


private
  variable
    ℓ ℓ' ℓ'' : Level

record IsSemiRing {R : Type ℓ}
              (0r 1r : R) (_+_ _⋆_ : R → R → R) : Type ℓ  where

  constructor issemiring

  field
    +IsCommMonoid  : IsCommMonoid 0r _+_
    ⋆IsCommMonoid  : IsCommMonoid 1r _⋆_
    dist           : (x y z : R) → (x ⋆ (y + z) ≡ (x ⋆ y) + (x ⋆ z))

  open IsCommMonoid ⋆IsCommMonoid public
    renaming
      ( assoc       to ⋆Assoc
      ; identity    to ⋆Identity
      ; lid         to ⋆Lid
      ; rid         to ⋆Rid
      ; isSemigroup to ⋆IsSemigroup
      ; comm        to ⋆comm )

  open IsCommMonoid +IsCommMonoid public
    renaming
      ( assoc       to +Assoc
      ; identity    to +Identity
      ; lid         to +Lid
      ; rid         to +Rid
      ; isSemigroup to +IsSemigroup
      ; comm        to +comm )
    hiding
      ( is-set ) -- We only want to export one proof of this

record SemiRingStr (R : Type ℓ) : Type ℓ  where
  field
    0r  : R
    1r  : R
    _+_ : R → R → R
    _⋆_ : R → R → R
    isSemiRing : IsSemiRing 0r 1r _+_ _⋆_

SemiRing : ∀ ℓ → Type (ℓ-suc ℓ) 
SemiRing _ = TypeWithStr _ SemiRingStr

record IsSemiRingHom {A : Type ℓ} {B : Type ℓ'} (Q : SemiRingStr A) (f : A → B) (W : SemiRingStr B)
  : Type (ℓ-max ℓ ℓ')
  where

  -- Shorter qualified names
  private
    module Q = SemiRingStr Q
    module W = SemiRingStr W

  field
    pres0 : f Q.0r ≡ W.0r
    pres1 : f Q.1r ≡ W.1r
    pres+ : (x y : A) → f (x Q.+ y) ≡ f x W.+ f y
    pres· : (x y : A) → f (x Q.⋆ y) ≡ f x W.⋆ f y

SemiRingHom : (L : SemiRing ℓ) (M : SemiRing ℓ') → Type _
SemiRingHom L M = Σ[ f ∈ (⟨ L ⟩ → ⟨ M ⟩) ] IsSemiRingHom (L .snd) f (M .snd)


