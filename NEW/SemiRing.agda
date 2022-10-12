{-# OPTIONS --cubical #-}

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

-- Derivation ?????
record IsSemiRingDer {A : Type ℓ} (Q : SemiRingStr A) (f : A → A)
  : Type ℓ
  where
  
  open SemiRingStr Q

  field
    pres0 : f 0r ≡ 0r
    pres1 : f 1r ≡ 0r
    pres+ : (x y : A) → f (x + y) ≡ f x + f y
    pres· : (x y : A) → f (x ⋆ y) ≡ (f x ⋆ y) + (x ⋆ f y)

SemiRingDer : (L : SemiRing ℓ) → Type _
SemiRingDer L = Σ[ f ∈ (⟨ L ⟩ → ⟨ L ⟩) ] IsSemiRingDer (L .snd) f


-- Bi-Derivation
record IsSemiRingBiDer {A : Type ℓ} (Q : SemiRingStr A) (f : A → A → A)
  : Type ℓ
  where
  
  open SemiRingStr Q

  field
    pres0l : (z : A) → f 0r z ≡ 0r
    pres1l : (z : A) → f 1r z ≡ 0r
    pres0r : (x : A) → f x 0r ≡ 0r
    pres1r : (x : A) → f x 1r ≡ 0r
    pres+l : (x y z : A) → f (x + y) z ≡ f x z + f y z
    pres+r : (x y z : A) → f z (x + y) ≡ f z x + f z y
    pres·l : (x y z : A) → f (x ⋆ y) z ≡ (f x z ⋆ y) + (x ⋆ f y z)
    pres·r : (x y z : A) → f z (x ⋆ y) ≡ (f z x ⋆ y) + (x ⋆ f z y)

SemiRingBiDer : (L : SemiRing ℓ) → Type _
SemiRingBiDer L = Σ[ f ∈ (⟨ L ⟩ → ⟨ L ⟩ → ⟨ L ⟩) ] IsSemiRingBiDer (L .snd) f

-- ? Necessary not
-- Bi-Derivation
record IsMonoidBiDer {A : Type ℓ} {C : Type ℓ'} (W : CommMonoidStr C) (Q : SemiRingStr A) (f : C → C → A)
  (id : C → A) : Type (ℓ-max ℓ ℓ')
  where
  
  module MW = CommMonoidStr W
  module MQ = SemiRingStr Q

  field
    pres1l : (z : C) → f MW.ε z ≡ MQ.0r
    pres1r : (x : C) → f x MW.ε ≡ MQ.0r
    pres·l : (x y z : C) → f (x MW.· y) z ≡ (f x z MQ.⋆ id y) MQ.+ (id x MQ.⋆ f y z)
    pres·r : (x y z : C) → f z (x MW.· y) ≡ (f z x MQ.⋆ id y) MQ.+ (id x MQ.⋆ f z y)

MonoidBiDer : (L : CommMonoid ℓ) (M : SemiRing ℓ') (id : ⟨ L ⟩ → ⟨ M ⟩) → Type _
MonoidBiDer L M id = Σ[ f ∈ (⟨ L ⟩ → ⟨ L ⟩ → ⟨ M ⟩) ] IsMonoidBiDer (L .snd) (M .snd) f id
