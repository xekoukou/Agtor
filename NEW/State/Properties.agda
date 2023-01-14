{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Vec as V
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat.Order.Recursive as O

import State
open import State.Lemma

module State.Properties where

module _ {ℓ} {C : ∀ k → Type ℓ} where

  open State C

  sucₛₛ-sucₛₛ :  ∀ n m → m ≤ n → ∀ q → sucₛₛ (sucₛₛ q m) (suc n) ≡ sucₛₛ (sucₛₛ q n) m 
  sucₛₛ-sucₛₛ n m m≤n 0b = refl
  sucₛₛ-sucₛₛ n m m≤n 1b = refl
  sucₛₛ-sucₛₛ n m m≤n (` [ secr ] c) = cong (λ vs → ` [ vs ] c) (lsuc-lsuc n m m≤n secr)
  sucₛₛ-sucₛₛ n m m≤n (q ∪ q₁) = cong₂ _∪_ (sucₛₛ-sucₛₛ n m m≤n q) (sucₛₛ-sucₛₛ n m m≤n q₁)
  sucₛₛ-sucₛₛ n m m≤n (q · q₁) = cong₂ _·_ (sucₛₛ-sucₛₛ n m m≤n q) (sucₛₛ-sucₛₛ n m m≤n q₁)
  sucₛₛ-sucₛₛ n m m≤n (ν q) = cong ν_ (sucₛₛ-sucₛₛ (suc n) (suc m) m≤n q)

  sucₛₛ-swapₛₛ : ∀ t m e → m < t → e < t → ∀ q → sucₛₛ (swapₛₛ m e q) t ≡ swapₛₛ m e (sucₛₛ q t)
  sucₛₛ-swapₛₛ t m e m<t e<t 0b = refl
  sucₛₛ-swapₛₛ t m e m<t e<t 1b = refl
  sucₛₛ-swapₛₛ t m e m<t e<t (` [ secr ] c) = cong (λ vs → ` ([ vs ] c)) (lsuc-lswap t m e m<t e<t secr)
  sucₛₛ-swapₛₛ t m e m<t e<t (q ∪ q₁) = cong₂ _∪_ (sucₛₛ-swapₛₛ t m e m<t e<t q)  (sucₛₛ-swapₛₛ t m e m<t e<t q₁)
  sucₛₛ-swapₛₛ t m e m<t e<t (q · q₁) = cong₂ _·_ (sucₛₛ-swapₛₛ t m e m<t e<t q) (sucₛₛ-swapₛₛ t m e m<t e<t q₁)
  sucₛₛ-swapₛₛ t m e m<t e<t (ν q) = cong ν_ (sucₛₛ-swapₛₛ (suc t) (suc m) (suc e) m<t e<t q)

  sucₛₛ-swapₛₛ> : ∀ t m e → t ≤ m → t ≤ e → ∀ q → sucₛₛ (swapₛₛ m e q) t ≡ swapₛₛ (suc m) (suc e) (sucₛₛ q t)
  sucₛₛ-swapₛₛ> t m e m>t e>t 0b = refl
  sucₛₛ-swapₛₛ> t m e m>t e>t 1b = refl
  sucₛₛ-swapₛₛ> t m e m>t e>t (` [ secr ] c) = cong (λ vs → ` ([ vs ] c)) (lsuc-lswap> t m e m>t e>t secr)
  sucₛₛ-swapₛₛ> t m e m>t e>t (q ∪ q₁) = cong₂ _∪_ (sucₛₛ-swapₛₛ> t m e m>t e>t q)  (sucₛₛ-swapₛₛ> t m e m>t e>t q₁)
  sucₛₛ-swapₛₛ> t m e m>t e>t (q · q₁) = cong₂ _·_ (sucₛₛ-swapₛₛ> t m e m>t e>t q) (sucₛₛ-swapₛₛ> t m e m>t e>t q₁)
  sucₛₛ-swapₛₛ> t m e m>t e>t (ν q) = cong ν_ (sucₛₛ-swapₛₛ> (suc t) (suc m) (suc e) m>t e>t q)



  swapₛₛ-swapₛₛ : ∀ t1 t2 e1 e2 → ¬ (t1 ≡ e1) → ¬ (t1 ≡ e2) →  ¬ (t2 ≡ e1) → ¬ (t2 ≡ e2) → ∀ q
                → swapₛₛ t1 t2 (swapₛₛ e1 e2 q) ≡ swapₛₛ e1 e2 (swapₛₛ t1 t2 q)
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 0b = refl
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 1b = refl
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 (` [ secr ] c) = cong (λ vs → ` ([ vs ] c)) (lswap-lswap t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 secr)
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 (q ∪ q₁) = cong₂ _∪_ (swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 q) (swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 q₁)
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 (q · q₁) = cong₂ _·_ (swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 q) (swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 q₁)
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 (ν q) = cong ν_ (swapₛₛ-swapₛₛ (suc t1) (suc t2) (suc e1) (suc e2) (t1≢e1 ∘ injSuc) (t1≢e2 ∘ injSuc) (t2≢e1 ∘ injSuc) (t2≢e2 ∘ injSuc) q)


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
  ⟨⟩-∪ {lbq1} {rbq1} {lbq2} {rbq2} eq1 eq2 i ∪` y = ElimProp.f (λ {z} → squash (⟨ lbq1 ∪ rbq1 ⟩ₛ ∪` z) (⟨ lbq2 ∪ rbq2 ⟩ₛ ∪` z))
    (⟨⟩-∪ (⟨⟩-∪ eq1 eq2) refl)
    (⟨⟩-∪ (⟨⟩-∪ eq1 eq2) refl)
    (λ ls c → ⟨⟩-∪ (⟨⟩-∪ eq1 eq2) refl)
    (λ lq rq → ⟨⟩-∪ (⟨⟩-∪ eq1 eq2) refl)
    (λ lq rq → ⟨⟩-∪ (⟨⟩-∪ eq1 eq2) refl)
    (λ q → ⟨⟩-∪ (⟨⟩-∪ eq1 eq2) refl)
    y i
  ⟨⟩-· {lbq1} {rbq1} {lbq2} {rbq2} eq1 eq2 i ∪` y = ElimProp.f (λ {z} → squash (⟨ lbq1 · rbq1 ⟩ₛ ∪` z) (⟨ lbq2 · rbq2 ⟩ₛ ∪` z))
    (⟨⟩-∪ (⟨⟩-· eq1 eq2) refl)
    (⟨⟩-∪ (⟨⟩-· eq1 eq2) refl)
    (λ ls c → ⟨⟩-∪ (⟨⟩-· eq1 eq2) refl)
    (λ lq rq → ⟨⟩-∪ (⟨⟩-· eq1 eq2) refl)
    (λ lq rq → ⟨⟩-∪ (⟨⟩-· eq1 eq2) refl)
    (λ q → ⟨⟩-∪ (⟨⟩-· eq1 eq2) refl)
    y i
  ⟨⟩-ν {q1} {q2} eq1 i ∪` y = ElimProp.f (λ {z} → squash (⟨ ν q1 ⟩ₛ ∪` z) (⟨ ν q2 ⟩ₛ ∪` z))
    (⟨⟩-∪ (⟨⟩-ν eq1) refl)
    (⟨⟩-∪ (⟨⟩-ν eq1) refl)
    (λ ls c → ⟨⟩-∪ (⟨⟩-ν eq1) refl)
    (λ lq rq → ⟨⟩-∪ (⟨⟩-ν eq1) refl)
    (λ lq rq → ⟨⟩-∪ (⟨⟩-ν eq1) refl)
    (λ q → ⟨⟩-∪ (⟨⟩-ν eq1) refl)
    y i
  ν-swap` qs i ∪` y =  ElimProp.f (λ {z} → squash (⟨ ν (ν swapₛₛ 0 1 qs) ⟩ₛ ∪` z) (⟨ ν (ν qs) ⟩ₛ ∪` z))
    (⟨⟩-∪ (ν-swap` qs) refl)
    (⟨⟩-∪ (ν-swap` qs) refl)
    (λ ls c → ⟨⟩-∪ (ν-swap` qs) refl)
    (λ lq rq → ⟨⟩-∪ (ν-swap` qs) refl)
    (λ lq rq → ⟨⟩-∪ (ν-swap` qs) refl)
    (λ q → ⟨⟩-∪ (ν-swap` qs) refl)
    y i
  ν-elim` qs i ∪` y =  ElimProp.f (λ {z} → squash (⟨ ν sucₛₛ qs 0 ⟩ₛ ∪` z) (⟨ qs ⟩ₛ ∪` z))
    (⟨⟩-∪ (ν-elim` qs) refl)
    (⟨⟩-∪ (ν-elim` qs) refl)
    (λ ls c → ⟨⟩-∪ (ν-elim` qs) refl)
    (λ lq rq → ⟨⟩-∪ (ν-elim` qs) refl)
    (λ lq rq → ⟨⟩-∪ (ν-elim` qs) refl)
    (λ q → ⟨⟩-∪ (ν-elim` qs) refl)
    y i
  ν-∪` qs zs i ∪` y =  ElimProp.f (λ {z} → squash (⟨ ν (zs ∪ sucₛₛ qs 0) ⟩ₛ ∪` z) (⟨ ν zs ∪ qs ⟩ₛ ∪` z))
    (⟨⟩-∪ (ν-∪` qs zs) refl)
    (⟨⟩-∪ (ν-∪` qs zs) refl)
    (λ ls c → ⟨⟩-∪ (ν-∪` qs zs) refl)
    (λ lq rq → ⟨⟩-∪ (ν-∪` qs zs) refl)
    (λ lq rq → ⟨⟩-∪ (ν-∪` qs zs) refl)
    (λ q → ⟨⟩-∪ (ν-∪` qs zs) refl)
    y i
  ν-·` qs zs i ∪` y =  ElimProp.f (λ {z} → squash (⟨ ν (zs · sucₛₛ qs 0) ⟩ₛ ∪` z) (⟨ ν zs · qs ⟩ₛ ∪` z))
    (⟨⟩-∪ (ν-·` qs zs) refl)
    (⟨⟩-∪ (ν-·` qs zs) refl)
    (λ ls c → ⟨⟩-∪ (ν-·` qs zs) refl)
    (λ lq rq → ⟨⟩-∪ (ν-·` qs zs) refl)
    (λ lq rq → ⟨⟩-∪ (ν-·` qs zs) refl)
    (λ q → ⟨⟩-∪ (ν-·` qs zs) refl)
    y i
  assoc x y₁ z i ∪` y =  ElimProp.f (λ {w} → squash (⟨ x ∪ y₁ ∪ z ⟩ₛ ∪` w) (⟨ (x ∪ y₁) ∪ z ⟩ₛ ∪` w))
    (⟨⟩-∪ (assoc x y₁ z) refl)
    (⟨⟩-∪ (assoc x y₁ z) refl)
    (λ ls c → ⟨⟩-∪ (assoc x y₁ z) refl)
    (λ lq rq → ⟨⟩-∪ (assoc x y₁ z) refl)
    (λ lq rq → ⟨⟩-∪ (assoc x y₁ z) refl)
    (λ q → ⟨⟩-∪ (assoc x y₁ z) refl)
    y i
  rid x i ∪` y =  ElimProp.f (λ {z} → squash (⟨ x ∪ 0b ⟩ₛ ∪` z) (⟨ x ⟩ₛ ∪` z))
    (⟨⟩-∪ (rid x) refl)
    (⟨⟩-∪ (rid x) refl)
    (λ ls c → ⟨⟩-∪ (rid x) refl)
    (λ lq rq → ⟨⟩-∪ (rid x) refl)
    (λ lq rq → ⟨⟩-∪ (rid x) refl)
    (λ q → ⟨⟩-∪ (rid x) refl)
    y i
  comm x y₁ i ∪` y =  ElimProp.f (λ {z} → squash (⟨ x ∪ y₁ ⟩ₛ ∪` z) (⟨ y₁ ∪ x ⟩ₛ ∪` z))
    (⟨⟩-∪ (comm x y₁) refl)
    (⟨⟩-∪ (comm x y₁) refl)
    (λ ls c → ⟨⟩-∪ (comm x y₁) refl)
    (λ lq rq → ⟨⟩-∪ (comm x y₁) refl)
    (λ lq rq → ⟨⟩-∪ (comm x y₁) refl)
    (λ q → ⟨⟩-∪ (comm x y₁) refl)
    y i
  idem x i ∪` y =  ElimProp.f (λ {z} → squash (⟨ x ∪ x ⟩ₛ ∪` z) (⟨ x ⟩ₛ ∪` z))
    (⟨⟩-∪ (idem x) refl)
    (⟨⟩-∪ (idem x) refl)
    (λ ls c → ⟨⟩-∪ (idem x) refl)
    (λ lq rq → ⟨⟩-∪ (idem x) refl)
    (λ lq rq → ⟨⟩-∪ (idem x) refl)
    (λ q → ⟨⟩-∪ (idem x) refl)
    y i
  assoc· x y₁ z i ∪` y =  ElimProp.f (λ {w} → squash (⟨ x · y₁ · z ⟩ₛ ∪` w) (⟨ (x · y₁) · z ⟩ₛ ∪` w))
    (⟨⟩-∪ (assoc· x y₁ z) refl)
    (⟨⟩-∪ (assoc· x y₁ z) refl)
    (λ ls c → ⟨⟩-∪ (assoc· x y₁ z) refl)
    (λ lq rq → ⟨⟩-∪ (assoc· x y₁ z) refl)
    (λ lq rq → ⟨⟩-∪ (assoc· x y₁ z) refl)
    (λ q → ⟨⟩-∪ (assoc· x y₁ z) refl)
    y i
  rid· x i ∪` y =  ElimProp.f (λ {z} → squash (⟨ x · 1b ⟩ₛ ∪` z) (⟨ x ⟩ₛ ∪` z))
    (⟨⟩-∪ (rid· x) refl)
    (⟨⟩-∪ (rid· x) refl)
    (λ ls c → ⟨⟩-∪ (rid· x) refl)
    (λ lq rq → ⟨⟩-∪ (rid· x) refl)
    (λ lq rq → ⟨⟩-∪ (rid· x) refl)
    (λ q → ⟨⟩-∪ (rid· x) refl)
    y i
  comm· x y₁ i ∪` y =  ElimProp.f (λ {z} → squash (⟨ x · y₁ ⟩ₛ ∪` z) (⟨ y₁ · x ⟩ₛ ∪` z))
    (⟨⟩-∪ (comm· x y₁) refl)
    (⟨⟩-∪ (comm· x y₁) refl)
    (λ ls c → ⟨⟩-∪ (comm· x y₁) refl)
    (λ lq rq → ⟨⟩-∪ (comm· x y₁) refl)
    (λ lq rq → ⟨⟩-∪ (comm· x y₁) refl)
    (λ q → ⟨⟩-∪ (comm· x y₁) refl)
    y i
  def∅· x i ∪` y =  ElimProp.f (λ {z} → squash (⟨ x · 0b ⟩ₛ ∪` z) (⟨ 0b ⟩ₛ ∪` z))
    (⟨⟩-∪ (def∅· x) refl)
    (⟨⟩-∪ (def∅· x) refl)
    (λ ls c → ⟨⟩-∪ (def∅· x) refl)
    (λ lq rq → ⟨⟩-∪ (def∅· x) refl)
    (λ lq rq → ⟨⟩-∪ (def∅· x) refl)
    (λ q → ⟨⟩-∪ (def∅· x) refl)
    y i
  dist x y₁ z i ∪` y =  ElimProp.f (λ {w} → squash (⟨ x · (y₁ ∪ z) ⟩ₛ ∪` w) (⟨ x · y₁ ∪ x · z ⟩ₛ ∪` w))
    (⟨⟩-∪ (dist x y₁ z) refl)
    (⟨⟩-∪ (dist x y₁ z) refl)
    (λ ls c → ⟨⟩-∪ (dist x y₁ z) refl)
    (λ lq rq → ⟨⟩-∪ (dist x y₁ z) refl)
    (λ lq rq → ⟨⟩-∪ (dist x y₁ z) refl)
    (λ q → ⟨⟩-∪ (dist x y₁ z) refl)
    y i
  squash x w p1 p2 i j ∪` y = squash (x ∪` y) (w ∪` y) (cong (_∪` y) p1) (cong (_∪` y) p2) i j

  {-# TERMINATING #-}
  _·`_ : (lq rq : State) → State
  ⟨ lq ⟩ₛ ·` ⟨ rq ⟩ₛ = ⟨ lq · rq ⟩ₛ
  ⟨ x ⟩ₛ ·` ⟨⟩-∪ eq1 eq2 i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (⟨⟩-∪ eq1 eq2)) i
  ⟨ x ⟩ₛ ·` ⟨⟩-· eq1 eq2 i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (⟨⟩-· eq1 eq2)) i
  ⟨ x ⟩ₛ ·` ⟨⟩-ν eq1 i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (⟨⟩-ν eq1)) i
  ⟨ x ⟩ₛ ·` ν-swap` qs i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (ν-swap` qs)) i
  ⟨ x ⟩ₛ ·` ν-elim` qs i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (ν-elim` qs)) i
  ⟨ x ⟩ₛ ·` ν-∪` qs zs i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (ν-∪` qs zs)) i
  ⟨ x ⟩ₛ ·` ν-·` qs zs i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (ν-·` qs zs)) i
  ⟨ x ⟩ₛ ·` assoc w y z i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (assoc w y z)) i
  ⟨ x ⟩ₛ ·` rid w i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (rid w)) i
  ⟨ x ⟩ₛ ·` comm w y i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (comm w y)) i
  ⟨ x ⟩ₛ ·` idem w i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (idem w)) i
  ⟨ x ⟩ₛ ·` assoc· w y z i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (assoc· w y z)) i
  ⟨ x ⟩ₛ ·` rid· w i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (rid· w)) i
  ⟨ x ⟩ₛ ·` comm· w y i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (comm· w y)) i
  ⟨ x ⟩ₛ ·` def∅· w i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (def∅· w)) i
  ⟨ x ⟩ₛ ·` dist w y z i = (⟨⟩-· (λ i → ⟨ x ⟩ₛ) (dist w y z)) i
  ⟨ x ⟩ₛ ·` squash w y p1 p2 i j = squash (⟨ x ⟩ₛ ·` w) (⟨ x ⟩ₛ ·` y) (cong (⟨ x ⟩ₛ ·`_) p1) (cong (⟨ x ⟩ₛ ·`_) p2) i j
  ⟨⟩-∪ {lbq1} {rbq1} {lbq2} {rbq2} eq1 eq2 i ·` y = ElimProp.f (λ {z} → squash (⟨ lbq1 ∪ rbq1 ⟩ₛ ·` z) (⟨ lbq2 ∪ rbq2 ⟩ₛ ·` z))
    (⟨⟩-· (⟨⟩-∪ eq1 eq2) refl)
    (⟨⟩-· (⟨⟩-∪ eq1 eq2) refl)
    (λ ls c → ⟨⟩-· (⟨⟩-∪ eq1 eq2) refl)
    (λ lq rq → ⟨⟩-· (⟨⟩-∪ eq1 eq2) refl)
    (λ lq rq → ⟨⟩-· (⟨⟩-∪ eq1 eq2) refl)
    (λ q → ⟨⟩-· (⟨⟩-∪ eq1 eq2) refl)
    y i
  ⟨⟩-· {lbq1} {rbq1} {lbq2} {rbq2} eq1 eq2 i ·` y = ElimProp.f (λ {z} → squash (⟨ lbq1 · rbq1 ⟩ₛ ·` z) (⟨ lbq2 · rbq2 ⟩ₛ ·` z))
    (⟨⟩-· (⟨⟩-· eq1 eq2) refl)
    (⟨⟩-· (⟨⟩-· eq1 eq2) refl)
    (λ ls c → ⟨⟩-· (⟨⟩-· eq1 eq2) refl)
    (λ lq rq → ⟨⟩-· (⟨⟩-· eq1 eq2) refl)
    (λ lq rq → ⟨⟩-· (⟨⟩-· eq1 eq2) refl)
    (λ q → ⟨⟩-· (⟨⟩-· eq1 eq2) refl)
    y i
  ⟨⟩-ν {q1} {q2} eq1 i ·` y = ElimProp.f (λ {z} → squash (⟨ ν q1 ⟩ₛ ·` z) (⟨ ν q2 ⟩ₛ ·` z))
    (⟨⟩-· (⟨⟩-ν eq1) refl)
    (⟨⟩-· (⟨⟩-ν eq1) refl)
    (λ ls c → ⟨⟩-· (⟨⟩-ν eq1) refl)
    (λ lq rq → ⟨⟩-· (⟨⟩-ν eq1) refl)
    (λ lq rq → ⟨⟩-· (⟨⟩-ν eq1) refl)
    (λ q → ⟨⟩-· (⟨⟩-ν eq1) refl)
    y i
  ν-swap` qs i ·` y =  ElimProp.f (λ {z} → squash (⟨ ν (ν swapₛₛ 0 1 qs) ⟩ₛ ·` z) (⟨ ν (ν qs) ⟩ₛ ·` z))
    (⟨⟩-· (ν-swap` qs) refl)
    (⟨⟩-· (ν-swap` qs) refl)
    (λ ls c → ⟨⟩-· (ν-swap` qs) refl)
    (λ lq rq → ⟨⟩-· (ν-swap` qs) refl)
    (λ lq rq → ⟨⟩-· (ν-swap` qs) refl)
    (λ q → ⟨⟩-· (ν-swap` qs) refl)
    y i
  ν-elim` qs i ·` y =  ElimProp.f (λ {z} → squash (⟨ ν sucₛₛ qs 0 ⟩ₛ ·` z) (⟨ qs ⟩ₛ ·` z))
    (⟨⟩-· (ν-elim` qs) refl)
    (⟨⟩-· (ν-elim` qs) refl)
    (λ ls c → ⟨⟩-· (ν-elim` qs) refl)
    (λ lq rq → ⟨⟩-· (ν-elim` qs) refl)
    (λ lq rq → ⟨⟩-· (ν-elim` qs) refl)
    (λ q → ⟨⟩-· (ν-elim` qs) refl)
    y i
  ν-∪` qs zs i ·` y =  ElimProp.f (λ {z} → squash (⟨ ν (zs ∪ sucₛₛ qs 0) ⟩ₛ ·` z) (⟨ ν zs ∪ qs ⟩ₛ ·` z))
    (⟨⟩-· (ν-∪` qs zs) refl)
    (⟨⟩-· (ν-∪` qs zs) refl)
    (λ ls c → ⟨⟩-· (ν-∪` qs zs) refl)
    (λ lq rq → ⟨⟩-· (ν-∪` qs zs) refl)
    (λ lq rq → ⟨⟩-· (ν-∪` qs zs) refl)
    (λ q → ⟨⟩-· (ν-∪` qs zs) refl)
    y i
  ν-·` qs zs i ·` y =  ElimProp.f (λ {z} → squash (⟨ ν (zs · sucₛₛ qs 0) ⟩ₛ ·` z) (⟨ ν zs · qs ⟩ₛ ·` z))
    (⟨⟩-· (ν-·` qs zs) refl)
    (⟨⟩-· (ν-·` qs zs) refl)
    (λ ls c → ⟨⟩-· (ν-·` qs zs) refl)
    (λ lq rq → ⟨⟩-· (ν-·` qs zs) refl)
    (λ lq rq → ⟨⟩-· (ν-·` qs zs) refl)
    (λ q → ⟨⟩-· (ν-·` qs zs) refl)
    y i
  assoc x y₁ z i ·` y =  ElimProp.f (λ {w} → squash (⟨ x ∪ y₁ ∪ z ⟩ₛ ·` w) (⟨ (x ∪ y₁) ∪ z ⟩ₛ ·` w))
    (⟨⟩-· (assoc x y₁ z) refl)
    (⟨⟩-· (assoc x y₁ z) refl)
    (λ ls c → ⟨⟩-· (assoc x y₁ z) refl)
    (λ lq rq → ⟨⟩-· (assoc x y₁ z) refl)
    (λ lq rq → ⟨⟩-· (assoc x y₁ z) refl)
    (λ q → ⟨⟩-· (assoc x y₁ z) refl)
    y i
  rid x i ·` y =  ElimProp.f (λ {z} → squash (⟨ x ∪ 0b ⟩ₛ ·` z) (⟨ x ⟩ₛ ·` z))
    (⟨⟩-· (rid x) refl)
    (⟨⟩-· (rid x) refl)
    (λ ls c → ⟨⟩-· (rid x) refl)
    (λ lq rq → ⟨⟩-· (rid x) refl)
    (λ lq rq → ⟨⟩-· (rid x) refl)
    (λ q → ⟨⟩-· (rid x) refl)
    y i
  comm x y₁ i ·` y =  ElimProp.f (λ {z} → squash (⟨ x ∪ y₁ ⟩ₛ ·` z) (⟨ y₁ ∪ x ⟩ₛ ·` z))
    (⟨⟩-· (comm x y₁) refl)
    (⟨⟩-· (comm x y₁) refl)
    (λ ls c → ⟨⟩-· (comm x y₁) refl)
    (λ lq rq → ⟨⟩-· (comm x y₁) refl)
    (λ lq rq → ⟨⟩-· (comm x y₁) refl)
    (λ q → ⟨⟩-· (comm x y₁) refl)
    y i
  idem x i ·` y =  ElimProp.f (λ {z} → squash (⟨ x ∪ x ⟩ₛ ·` z) (⟨ x ⟩ₛ ·` z))
    (⟨⟩-· (idem x) refl)
    (⟨⟩-· (idem x) refl)
    (λ ls c → ⟨⟩-· (idem x) refl)
    (λ lq rq → ⟨⟩-· (idem x) refl)
    (λ lq rq → ⟨⟩-· (idem x) refl)
    (λ q → ⟨⟩-· (idem x) refl)
    y i
  assoc· x y₁ z i ·` y =  ElimProp.f (λ {w} → squash (⟨ x · y₁ · z ⟩ₛ ·` w) (⟨ (x · y₁) · z ⟩ₛ ·` w))
    (⟨⟩-· (assoc· x y₁ z) refl)
    (⟨⟩-· (assoc· x y₁ z) refl)
    (λ ls c → ⟨⟩-· (assoc· x y₁ z) refl)
    (λ lq rq → ⟨⟩-· (assoc· x y₁ z) refl)
    (λ lq rq → ⟨⟩-· (assoc· x y₁ z) refl)
    (λ q → ⟨⟩-· (assoc· x y₁ z) refl)
    y i
  rid· x i ·` y =  ElimProp.f (λ {z} → squash (⟨ x · 1b ⟩ₛ ·` z) (⟨ x ⟩ₛ ·` z))
    (⟨⟩-· (rid· x) refl)
    (⟨⟩-· (rid· x) refl)
    (λ ls c → ⟨⟩-· (rid· x) refl)
    (λ lq rq → ⟨⟩-· (rid· x) refl)
    (λ lq rq → ⟨⟩-· (rid· x) refl)
    (λ q → ⟨⟩-· (rid· x) refl)
    y i
  comm· x y₁ i ·` y =  ElimProp.f (λ {z} → squash (⟨ x · y₁ ⟩ₛ ·` z) (⟨ y₁ · x ⟩ₛ ·` z))
    (⟨⟩-· (comm· x y₁) refl)
    (⟨⟩-· (comm· x y₁) refl)
    (λ ls c → ⟨⟩-· (comm· x y₁) refl)
    (λ lq rq → ⟨⟩-· (comm· x y₁) refl)
    (λ lq rq → ⟨⟩-· (comm· x y₁) refl)
    (λ q → ⟨⟩-· (comm· x y₁) refl)
    y i
  def∅· x i ·` y =  ElimProp.f (λ {z} → squash (⟨ x · 0b ⟩ₛ ·` z) (⟨ 0b ⟩ₛ ·` z))
    (⟨⟩-· (def∅· x) refl)
    (⟨⟩-· (def∅· x) refl)
    (λ ls c → ⟨⟩-· (def∅· x) refl)
    (λ lq rq → ⟨⟩-· (def∅· x) refl)
    (λ lq rq → ⟨⟩-· (def∅· x) refl)
    (λ q → ⟨⟩-· (def∅· x) refl)
    y i
  dist x y₁ z i ·` y =  ElimProp.f (λ {w} → squash (⟨ x · (y₁ ∪ z) ⟩ₛ ·` w) (⟨ x · y₁ ∪ x · z ⟩ₛ ·` w))
    (⟨⟩-· (dist x y₁ z) refl)
    (⟨⟩-· (dist x y₁ z) refl)
    (λ ls c → ⟨⟩-· (dist x y₁ z) refl)
    (λ lq rq → ⟨⟩-· (dist x y₁ z) refl)
    (λ lq rq → ⟨⟩-· (dist x y₁ z) refl)
    (λ q → ⟨⟩-· (dist x y₁ z) refl)
    y i
  squash x w p1 p2 i j ·` y = squash (x ·` y) (w ·` y) (cong (_·` y) p1) (cong (_·` y) p2) i j

  {-# TERMINATING #-}
  ν`_ : (q : State) → State
  ν` ⟨ x ⟩ₛ = ⟨ ν x ⟩ₛ
  ν` ⟨⟩-∪ x x₁ i = ⟨⟩-ν (⟨⟩-∪ x x₁) i
  ν` ⟨⟩-· x x₁ i = ⟨⟩-ν (⟨⟩-· x x₁) i
  ν` ⟨⟩-ν x i = ⟨⟩-ν (⟨⟩-ν x) i
  ν` ν-swap` qs i = ⟨⟩-ν (ν-swap` qs) i
  ν` ν-elim` qs i = ⟨⟩-ν (ν-elim` qs) i
  ν` ν-∪` qs zs i = ⟨⟩-ν (ν-∪` qs zs) i
  ν` ν-·` qs zs i = ⟨⟩-ν (ν-·` qs zs) i
  ν` assoc x y z i = ⟨⟩-ν (assoc x y z) i
  ν` rid x i = ⟨⟩-ν (rid x) i
  ν` comm x y i = ⟨⟩-ν (comm x y) i
  ν` idem x i = ⟨⟩-ν (idem x) i
  ν` assoc· x y z i = ⟨⟩-ν (assoc· x y z) i
  ν` rid· x i = ⟨⟩-ν (rid· x) i
  ν` comm· x y i = ⟨⟩-ν (comm· x y) i
  ν` def∅· x i = ⟨⟩-ν (def∅· x ) i
  ν` dist x y z i = ⟨⟩-ν (dist x y z) i
  ν` squash x y p1 p2 i j = squash (ν` x) (ν` y) (cong ν`_ p1) (cong ν`_ p2) i j

  sucₛ : ∀ n → State → State
  sucₛ n ⟨ x ⟩ₛ = ⟨ sucₛₛ x n ⟩ₛ
  sucₛ n (⟨⟩-∪ x x₁ i) = ⟨⟩-∪ (cong (sucₛ n) x) (cong (sucₛ n) x₁) i
  sucₛ n (⟨⟩-· x x₁ i) = ⟨⟩-· (cong (sucₛ n) x) (cong (sucₛ n) x₁) i
  sucₛ n (⟨⟩-ν x i) = ⟨⟩-ν (cong (sucₛ (suc n)) x) i
  sucₛ n (ν-swap` qs i) = ((cong (λ x → ⟨ ν (ν x) ⟩ₛ) (sucₛₛ-swapₛₛ (2 + n) 0 1 tt tt qs)) ∙ ν-swap` (sucₛₛ qs (2 + n))) i
  sucₛ n (ν-elim` qs i) = (cong (λ a → ⟨ ν a ⟩ₛ) (sucₛₛ-sucₛₛ n 0 tt qs) ∙ ν-elim` (sucₛₛ qs n)) i
  sucₛ n (ν-∪` qs zs i) = (cong (λ a → ⟨ ν (sucₛₛ zs (suc n) ∪ a) ⟩ₛ) (sucₛₛ-sucₛₛ n 0 tt qs) ∙ ν-∪` (sucₛₛ qs n) (sucₛₛ zs (suc n))) i
  sucₛ n (ν-·` qs zs i) = (cong (λ a → ⟨ ν (sucₛₛ zs (suc n) · a) ⟩ₛ) (sucₛₛ-sucₛₛ n 0 tt qs) ∙ ν-·` (sucₛₛ qs n) (sucₛₛ zs (suc n))) i
  sucₛ n (assoc x y z i) = assoc (sucₛₛ x n) (sucₛₛ y n) (sucₛₛ z n) i
  sucₛ n (rid x i) = rid (sucₛₛ x n) i
  sucₛ n (comm x y i) = comm (sucₛₛ x n) (sucₛₛ y n) i
  sucₛ n (idem x i) = idem (sucₛₛ x n) i
  sucₛ n (assoc· x y z i) = assoc· (sucₛₛ x n) (sucₛₛ y n) (sucₛₛ z n) i
  sucₛ n (rid· x i) = rid· (sucₛₛ x n) i
  sucₛ n (comm· x y i) = comm· (sucₛₛ x n) (sucₛₛ y n) i
  sucₛ n (def∅· x i) = def∅· (sucₛₛ x n) i
  sucₛ n (dist x y z i) = dist (sucₛₛ x n) (sucₛₛ y n) (sucₛₛ z n) i
  sucₛ n (squash a b p1 p2 i j) = squash (sucₛ n a) (sucₛ n b) (cong (sucₛ n) p1) (cong (sucₛ n) p2) i j


  swapₛ : ∀ n m → State → State
  swapₛ n m ⟨ q ⟩ₛ = ⟨ swapₛₛ n m q ⟩ₛ
  swapₛ n m (⟨⟩-∪ x x₁ i) = ⟨⟩-∪ (cong (swapₛ n m) x) (cong (swapₛ n m) x₁) i
  swapₛ n m (⟨⟩-· x x₁ i) = ⟨⟩-· (cong (swapₛ n m) x) (cong (swapₛ n m) x₁) i
  swapₛ n m (⟨⟩-ν q i) = ⟨⟩-ν (cong (swapₛ (suc n) (suc m)) q) i
  swapₛ n m (ν-swap` qs i) = (cong (λ a → ⟨ ν ν a ⟩ₛ) (swapₛₛ-swapₛₛ (2 + n) (2 + m) 0 1 snotz (snotz ∘ injSuc) snotz (snotz ∘ injSuc) qs) ∙ ν-swap` (swapₛₛ (2 + n) (2 + m) qs)) i
  swapₛ n m (ν-elim` qs i) = (cong (λ a → ⟨ ν a ⟩ₛ) (sym (sucₛₛ-swapₛₛ> 0 n m tt tt qs)) ∙ ν-elim` (swapₛₛ n m qs)) i
  swapₛ n m (ν-∪` qs zs i) = (cong (λ a → ⟨ ν (swapₛₛ (suc n) (suc m) zs ∪ a) ⟩ₛ) (sym (sucₛₛ-swapₛₛ> 0 n m tt tt qs)) ∙ ν-∪` (swapₛₛ n m qs) (swapₛₛ (suc n) (suc m) zs)) i
  swapₛ n m (ν-·` qs zs i) = (cong (λ a → ⟨ ν (swapₛₛ (suc n) (suc m) zs · a) ⟩ₛ) (sym (sucₛₛ-swapₛₛ> 0 n m tt tt qs)) ∙ ν-·` (swapₛₛ n m qs) (swapₛₛ (suc n) (suc m) zs)) i
  swapₛ n m (assoc x y z i) = assoc (swapₛₛ n m x) (swapₛₛ n m y) (swapₛₛ n m z) i
  swapₛ n m (rid x i) = rid (swapₛₛ n m x) i
  swapₛ n m (comm x y i) = comm (swapₛₛ n m x) (swapₛₛ n m y) i
  swapₛ n m (idem x i) = idem (swapₛₛ n m x) i
  swapₛ n m (assoc· x y z i) = assoc· (swapₛₛ n m x) (swapₛₛ n m y) (swapₛₛ n m z) i
  swapₛ n m (rid· x i) = rid· (swapₛₛ n m x) i
  swapₛ n m (comm· x y i) = comm· (swapₛₛ n m x) (swapₛₛ n m y) i
  swapₛ n m (def∅· x i) = def∅· (swapₛₛ n m x) i
  swapₛ n m (dist x y z i) = dist (swapₛₛ n m x) (swapₛₛ n m y) (swapₛₛ n m z) i
  swapₛ n m (squash a b p1 p2 i j) = squash (swapₛ n m a) (swapₛ n m b) (cong (swapₛ n m) p1) (cong (swapₛ n m) p2) i j


  WellScopedₛ : State → ℕ → Type ℓ
  WellScopedₛ ⟨ x ⟩ₛ n = WellScopedₛₛ x n
  WellScopedₛ (⟨⟩-∪ x x₁ i) n = {!!}
  WellScopedₛ (⟨⟩-· x x₁ i) n = {!!}
  WellScopedₛ (⟨⟩-ν x i) n = {!!}
  WellScopedₛ (ν-swap` qs i) n = {!!}
  WellScopedₛ (ν-elim` qs i) n = {!!}
  WellScopedₛ (ν-∪` qs zs i) n = {!!}
  WellScopedₛ (ν-·` qs zs i) n = {!!}
  WellScopedₛ (assoc x y z i) n = {!!}
  WellScopedₛ (rid x i) n = {!!}
  WellScopedₛ (comm x y i) n = {!!}
  WellScopedₛ (idem x i) n = {!!}
  WellScopedₛ (assoc· x y z i) n = {!!}
  WellScopedₛ (rid· x i) n = {!!}
  WellScopedₛ (comm· x y i) n = {!!}
  WellScopedₛ (def∅· x i) n = {!!}
  WellScopedₛ (dist x y z i) n = {!!}
  WellScopedₛ (squash s s₁ x y i i₁) n = {!!}



--   AllisProp` : ∀{e ls k} → isProp (All {e} ls k)
--   AllisProp` {ls = []} = isPropUnit
--   AllisProp` {ls = x ∷ ls} {k} = isProp× (O.isProp≤ {suc x} {k}) AllisProp`
  
-- --   WSisProp` : (s : SState) → ∀ k → isProp (WellScoped s k)
-- --   WSisProp` ⟨ 0bₛ ⟩ₛ k = isPropUnit
-- --   WSisProp` ⟨ 1bₛ ⟩ₛ k = isPropUnit
-- --   WSisProp` ⟨ `[ ls ]ₛ c ⟩ₛ k = AllisProp` {_} {ls} {k}
-- --   WSisProp` ⟨ s₁ ∪ₛ s₂ ⟩ₛ k = isProp× (WSisProp` ⟨ s₁ ⟩ₛ k) (WSisProp` ⟨ s₂ ⟩ₛ k)
-- --   WSisProp` ⟨ s₁ ·ₛ s₂ ⟩ₛ k = isProp× (WSisProp` ⟨ s₁ ⟩ₛ k) (WSisProp` ⟨ s₂ ⟩ₛ k)
-- --   WSisProp` ⟨ νₛ s₁ ⟩ₛ k = WSisProp` ⟨ s₁ ⟩ₛ (suc k)

-- --   WSisProp : (s : SState) → isProp (∀ k → WellScoped s k)
-- --   WSisProp s = isPropΠ (WSisProp` s)



-- -- module _ {ℓ1} {ℓ2} {C1 : ∀ k → Type ℓ1} {C2 : ∀ k → Type ℓ2} where

-- --   module St1 = State C1
-- --   module St2 = State C2

-- --   mutual

-- --     {-# TERMINATING #-}
-- --     mapₛ : (∀{k} → C1 k → C2 k) → St1.State → St2.State
-- --     mapₛ f St1.0b = St2.0b
-- --     mapₛ f St1.1b = St2.1b
-- --     mapₛ f (State.`[ ls ] x) = St2.`[ ls ] f x
-- --     mapₛ f (x St1.∪ x₁) = mapₛ f x St2.∪ mapₛ f x₁
-- --     mapₛ f (x St1.· x₁) = mapₛ f x St2.· mapₛ f x₁
-- --     mapₛ f (St1.ν x) = St2.ν mapₛ f x
-- --     mapₛ f (St1.ν-elim x i) = ((cong St2.ν_ (mapₛ-suc {0} f x)) ∙ St2.ν-elim (mapₛ f x)) i
-- --     mapₛ f (St1.ν-∪ x x₁ i) = (cong (λ w → St2.ν (mapₛ f x St2.∪ w)) (mapₛ-suc {0} f x₁) ∙ St2.ν-∪ (mapₛ f x) (mapₛ f x₁)) i
-- --     mapₛ f (St1.ν-· x x₁ i) = (cong (λ w → St2.ν (mapₛ f x St2.· w)) (mapₛ-suc {0} f x₁) ∙ St2.ν-· (mapₛ f x) (mapₛ f x₁)) i
-- --     mapₛ f (St1.squash a b p1 p2 i j) = isOfHLevel→isOfHLevelDep 2 (λ a₁ → St2.squash)  (mapₛ f a) (mapₛ f b) (cong (mapₛ f) p1) (cong (mapₛ f) p2) (St1.squash a b p1 p2) i j
-- --     mapₛ f (St1.assoc x x₁ x₂ i) = St2.assoc (mapₛ f x) (mapₛ f x₁) (mapₛ f x₂) i
-- --     mapₛ f (St1.rid x i) = St2.rid (mapₛ f x) i
-- --     mapₛ f (St1.comm x x₁ i) = St2.comm (mapₛ f x) (mapₛ f x₁) i
-- --     mapₛ f (St1.idem x i) = St2.idem (mapₛ f x) i
-- --     mapₛ f (St1.assoc· x x₁ x₂ i) = St2.assoc· (mapₛ f x) (mapₛ f x₁) (mapₛ f x₂) i
-- --     mapₛ f (St1.rid· x i) = St2.rid· (mapₛ f x) i
-- --     mapₛ f (St1.comm· x x₁ i) = St2.comm· (mapₛ f x) (mapₛ f x₁) i
-- --     mapₛ f (St1.def∅· x i) = St2.def∅· (mapₛ f x) i
-- --     mapₛ f (St1.dist x x₁ x₂ i) = St2.dist (mapₛ f x) (mapₛ f x₁) (mapₛ f x₂) i

-- --     mapₛ-suc : ∀ {n} → (f : ∀{k} → C1 k → C2 k) → ∀ x → mapₛ f (St1.sucₛ n x) ≡ St2.sucₛ n (mapₛ f x)
-- --     mapₛ-suc {n} f x = St1.ElimProp.f {B = λ x → (n : ℕ) → mapₛ f (St1.sucₛ n x) ≡ St2.sucₛ n (mapₛ f x)}
-- --                            (λ a b i n → St2.squash _ _ (a n) (b n) i )
-- --                            (λ _ → refl)
-- --                            (λ _ → refl)
-- --                            (λ { ls x → (λ _ → refl) })
-- --                            (λ x x₁ → λ n → cong₂ St2._∪_ (x n) (x₁ n))
-- --                            (λ x x₁ → λ n → cong₂ St2._·_ (x n) (x₁ n))
-- --                            (λ x → λ n → cong St2.ν_ (x (suc n)))
-- --                            x n


-- --   mapₛ-StrSt : {s : St1.State} → (f : ∀{k} → C1 k → C2 k) → St1.IsStrSt s → St2.IsStrSt (mapₛ f s)
-- --   mapₛ-StrSt f St1.0bₛ = St2.0bₛ
-- --   mapₛ-StrSt f St1.1bₛ = St2.1bₛ
-- --   mapₛ-StrSt f (St1.`[_]ₛ_ _ _) = St2.`[_]ₛ_ _ _
-- --   mapₛ-StrSt f (St1._∪ₛ_ x x₁) = St2._∪ₛ_ (mapₛ-StrSt f x) (mapₛ-StrSt f x₁)
-- --   mapₛ-StrSt f (St1._·ₛ_ x x₁) = St2._·ₛ_ (mapₛ-StrSt f x) (mapₛ-StrSt f x₁)
-- --   mapₛ-StrSt f (St1.νₛ_ x) = St2.νₛ_ (mapₛ-StrSt f x)
