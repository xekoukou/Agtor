{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Vec as V
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat.Order.Recursive as O

import State

module State.Properties where

module _ {ℓ} {C : ∀ k → Type ℓ} where

  open State C

  {-# TERMINATING #-}
  _∪`_ : (lq rq : State) → State
  ⟨ lq ⟩ₛ ∪` ⟨ rq ⟩ₛ = ⟨ lq ∪ rq ⟩ₛ
  ⟨ x ⟩ₛ ∪` ⟨⟩-∪ eq1 eq2 i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (⟨⟩-∪ eq1 eq2)) i
  ⟨ x ⟩ₛ ∪` ⟨⟩-· eq1 eq2 i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (⟨⟩-· eq1 eq2)) i
  ⟨ x ⟩ₛ ∪` ⟨⟩-ν eq1 i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (⟨⟩-ν eq1)) i
  ⟨ x ⟩ₛ ∪` ν-swap` qs i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (ν-swap` qs)) i
  ⟨ x ⟩ₛ ∪` ν-elim` qs i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (ν-elim` qs)) i
  ⟨ x ⟩ₛ ∪` ν-∪` qs zs i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (ν-∪` qs zs)) i
  ⟨ x ⟩ₛ ∪` ν-·` qs zs i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (ν-·` qs zs)) i
  ⟨ x ⟩ₛ ∪` assoc w y z i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (assoc w y z)) i
  ⟨ x ⟩ₛ ∪` rid w i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (rid w)) i
  ⟨ x ⟩ₛ ∪` comm w y i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (comm w y)) i
  ⟨ x ⟩ₛ ∪` idem w i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (idem w)) i
  ⟨ x ⟩ₛ ∪` assoc· w y z i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (assoc· w y z)) i
  ⟨ x ⟩ₛ ∪` rid· w i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (rid· w)) i
  ⟨ x ⟩ₛ ∪` comm· w y i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (comm· w y)) i
  ⟨ x ⟩ₛ ∪` def∅· w i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (def∅· w)) i
  ⟨ x ⟩ₛ ∪` dist w y z i = (⟨⟩-∪ (λ i → ⟨ x ⟩ₛ) (dist w y z)) i
  ⟨ x ⟩ₛ ∪` squash w y p1 p2 i j = squash (⟨ x ⟩ₛ ∪` w) (⟨ x ⟩ₛ ∪` y) (cong (⟨ x ⟩ₛ ∪`_) p1) (cong (⟨ x ⟩ₛ ∪`_) p2) i j
  ⟨⟩-∪ {lbq1} {rbq1} {lbq2} {rbq2} eq1 eq2 i ∪` y = ElimProp.f (λ {z} → squash (⟨ lbq1 ∪ rbq1 ⟩ₛ ∪` z) (⟨ lbq2 ∪ rbq2 ⟩ₛ ∪` z)) {!!} {!!} {!!} {!!} {!!} {!!} y i where
    l1 = cong (λ a → a ∪` y) eq1
    l2 = cong (λ a → a ∪` y) eq2
  ⟨⟩-· eq1 eq2 i ∪` y = {!!}
  ⟨⟩-ν eq1 i ∪` y = {!!}
  ν-swap` qs i ∪` y = {!!}
  ν-elim` qs i ∪` y = {!!}
  ν-∪` qs zs i ∪` y = {!!}
  ν-·` qs zs i ∪` y = {!!}
  assoc x y₁ z i ∪` y = {!!}
  rid x i ∪` y = {!!}
  comm x y₁ i ∪` y = {!!}
  idem x i ∪` y = {!!}
  assoc· x y₁ z i ∪` y = {!!}
  rid· x i ∪` y = {!!}
  comm· x y₁ i ∪` y = {!!}
  def∅· x i ∪` y = {!!}
  dist x y₁ z i ∪` y = {!!}
  squash x x₁ x₂ y₁ i i₁ ∪` y = {!!}

  
--   AllisProp` : ∀{e ls k} → isProp (All {e} ls k)
--   AllisProp` {ls = []} = isPropUnit
--   AllisProp` {ls = x ∷ ls} {k} = isProp× (O.isProp≤ {suc x} {k}) AllisProp`
  
--   WSisProp` : (s : SState) → ∀ k → isProp (WellScoped s k)
--   WSisProp` ⟨ 0bₛ ⟩ₛ k = isPropUnit
--   WSisProp` ⟨ 1bₛ ⟩ₛ k = isPropUnit
--   WSisProp` ⟨ `[ ls ]ₛ c ⟩ₛ k = AllisProp` {_} {ls} {k}
--   WSisProp` ⟨ s₁ ∪ₛ s₂ ⟩ₛ k = isProp× (WSisProp` ⟨ s₁ ⟩ₛ k) (WSisProp` ⟨ s₂ ⟩ₛ k)
--   WSisProp` ⟨ s₁ ·ₛ s₂ ⟩ₛ k = isProp× (WSisProp` ⟨ s₁ ⟩ₛ k) (WSisProp` ⟨ s₂ ⟩ₛ k)
--   WSisProp` ⟨ νₛ s₁ ⟩ₛ k = WSisProp` ⟨ s₁ ⟩ₛ (suc k)

--   WSisProp : (s : SState) → isProp (∀ k → WellScoped s k)
--   WSisProp s = isPropΠ (WSisProp` s)



-- module _ {ℓ1} {ℓ2} {C1 : ∀ k → Type ℓ1} {C2 : ∀ k → Type ℓ2} where

--   module St1 = State C1
--   module St2 = State C2

--   mutual

--     {-# TERMINATING #-}
--     mapₛ : (∀{k} → C1 k → C2 k) → St1.State → St2.State
--     mapₛ f St1.0b = St2.0b
--     mapₛ f St1.1b = St2.1b
--     mapₛ f (State.`[ ls ] x) = St2.`[ ls ] f x
--     mapₛ f (x St1.∪ x₁) = mapₛ f x St2.∪ mapₛ f x₁
--     mapₛ f (x St1.· x₁) = mapₛ f x St2.· mapₛ f x₁
--     mapₛ f (St1.ν x) = St2.ν mapₛ f x
--     mapₛ f (St1.ν-elim x i) = ((cong St2.ν_ (mapₛ-suc {0} f x)) ∙ St2.ν-elim (mapₛ f x)) i
--     mapₛ f (St1.ν-∪ x x₁ i) = (cong (λ w → St2.ν (mapₛ f x St2.∪ w)) (mapₛ-suc {0} f x₁) ∙ St2.ν-∪ (mapₛ f x) (mapₛ f x₁)) i
--     mapₛ f (St1.ν-· x x₁ i) = (cong (λ w → St2.ν (mapₛ f x St2.· w)) (mapₛ-suc {0} f x₁) ∙ St2.ν-· (mapₛ f x) (mapₛ f x₁)) i
--     mapₛ f (St1.squash a b p1 p2 i j) = isOfHLevel→isOfHLevelDep 2 (λ a₁ → St2.squash)  (mapₛ f a) (mapₛ f b) (cong (mapₛ f) p1) (cong (mapₛ f) p2) (St1.squash a b p1 p2) i j
--     mapₛ f (St1.assoc x x₁ x₂ i) = St2.assoc (mapₛ f x) (mapₛ f x₁) (mapₛ f x₂) i
--     mapₛ f (St1.rid x i) = St2.rid (mapₛ f x) i
--     mapₛ f (St1.comm x x₁ i) = St2.comm (mapₛ f x) (mapₛ f x₁) i
--     mapₛ f (St1.idem x i) = St2.idem (mapₛ f x) i
--     mapₛ f (St1.assoc· x x₁ x₂ i) = St2.assoc· (mapₛ f x) (mapₛ f x₁) (mapₛ f x₂) i
--     mapₛ f (St1.rid· x i) = St2.rid· (mapₛ f x) i
--     mapₛ f (St1.comm· x x₁ i) = St2.comm· (mapₛ f x) (mapₛ f x₁) i
--     mapₛ f (St1.def∅· x i) = St2.def∅· (mapₛ f x) i
--     mapₛ f (St1.dist x x₁ x₂ i) = St2.dist (mapₛ f x) (mapₛ f x₁) (mapₛ f x₂) i

--     mapₛ-suc : ∀ {n} → (f : ∀{k} → C1 k → C2 k) → ∀ x → mapₛ f (St1.sucₛ n x) ≡ St2.sucₛ n (mapₛ f x)
--     mapₛ-suc {n} f x = St1.ElimProp.f {B = λ x → (n : ℕ) → mapₛ f (St1.sucₛ n x) ≡ St2.sucₛ n (mapₛ f x)}
--                            (λ a b i n → St2.squash _ _ (a n) (b n) i )
--                            (λ _ → refl)
--                            (λ _ → refl)
--                            (λ { ls x → (λ _ → refl) })
--                            (λ x x₁ → λ n → cong₂ St2._∪_ (x n) (x₁ n))
--                            (λ x x₁ → λ n → cong₂ St2._·_ (x n) (x₁ n))
--                            (λ x → λ n → cong St2.ν_ (x (suc n)))
--                            x n


--   mapₛ-StrSt : {s : St1.State} → (f : ∀{k} → C1 k → C2 k) → St1.IsStrSt s → St2.IsStrSt (mapₛ f s)
--   mapₛ-StrSt f St1.0bₛ = St2.0bₛ
--   mapₛ-StrSt f St1.1bₛ = St2.1bₛ
--   mapₛ-StrSt f (St1.`[_]ₛ_ _ _) = St2.`[_]ₛ_ _ _
--   mapₛ-StrSt f (St1._∪ₛ_ x x₁) = St2._∪ₛ_ (mapₛ-StrSt f x) (mapₛ-StrSt f x₁)
--   mapₛ-StrSt f (St1._·ₛ_ x x₁) = St2._·ₛ_ (mapₛ-StrSt f x) (mapₛ-StrSt f x₁)
--   mapₛ-StrSt f (St1.νₛ_ x) = St2.νₛ_ (mapₛ-StrSt f x)
