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
open import Cubical.HITs.SetQuotients as SQ renaming ([_] to ⟨_⟩ₛ)

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


  _∪`_ : (lq rq : State) → State
  lq ∪` rq = SQ.rec squash/ (λ lq → SQ.rec squash/ (λ rq → ⟨ lq ∪ rq ⟩ₛ) l1 rq) (l2 rq) lq where
    l1 : {lq : SState} (a b : SState) →
         a R b → ⟨ lq ∪ a ⟩ₛ ≡ ⟨ lq ∪ b ⟩ₛ
    l1 {lq} _ _ R1 = eq/ _ _ (⟨⟩-∪ (refl` _) R1)
    l2 : (rq : State) → (a b : SState) →
         a R b → 
         SQ.rec squash/ (λ rq → ⟨ a ∪ rq ⟩ₛ) l1 rq
         ≡
         SQ.rec squash/ (λ rq → ⟨ b ∪ rq ⟩ₛ) l1 rq
    l2 rq a b R1 = SQ.elimProp {P = λ z → SQ.rec squash/ (λ rq → ⟨ a ∪ rq ⟩ₛ) l1 z
         ≡
         SQ.rec squash/ (λ rq → ⟨ b ∪ rq ⟩ₛ) l1 z} (λ z → squash/ _ _) (λ rq → eq/ (a ∪ rq) (b ∪ rq) (⟨⟩-∪ R1 (refl` _))) rq 

  _·`_ : (lq rq : State) → State
  lq ·` rq = SQ.rec squash/ (λ lq → SQ.rec squash/ (λ rq → ⟨ lq · rq ⟩ₛ) l1 rq) (l2 rq) lq where
    l1 : {lq : SState} (a b : SState) →
         a R b → ⟨ lq · a ⟩ₛ ≡ ⟨ lq · b ⟩ₛ
    l1 {lq} _ _ R1 = eq/ _ _ (⟨⟩-· (refl` _) R1)
    l2 : (rq : State) → (a b : SState) →
         a R b → 
         SQ.rec squash/ (λ rq → ⟨ a · rq ⟩ₛ) l1 rq
         ≡
         SQ.rec squash/ (λ rq → ⟨ b · rq ⟩ₛ) l1 rq
    l2 rq a b R1 = SQ.elimProp {P = λ z → SQ.rec squash/ (λ rq → ⟨ a · rq ⟩ₛ) l1 z
         ≡
         SQ.rec squash/ (λ rq → ⟨ b · rq ⟩ₛ) l1 z} (λ z → squash/ _ _) (λ rq → eq/ (a · rq) (b · rq) (⟨⟩-· R1 (refl` _))) rq 

  ν`_ : (q : State) → State
  ν`_ q = SQ.rec squash/ (λ x → ⟨ ν x ⟩ₛ) l1 q where
    l1 : (a b : SState) → a R b → ⟨ ν a ⟩ₛ ≡ ⟨ ν b ⟩ₛ
    l1 a b R1 = eq/ _ _ (⟨⟩-ν R1)

  sucₛ : ∀ n → State → State
  sucₛ n q = SQ.elim (λ _ → squash/) (λ a → ⟨ sucₛₛ a n ⟩ₛ) (l1 n) q where
    l1 : (n : ℕ) (a b : SState) (r : a R b) → ⟨ sucₛₛ a n ⟩ₛ ≡ ⟨ sucₛₛ b n ⟩ₛ
    l1 n .(_ ∪ _) .(_ ∪ _) (⟨⟩-∪ r r₁) = ?
    l1 n .(_ · _) .(_ · _) (⟨⟩-· r r₁) = ?
    l1 n .(ν _) .(ν _) (⟨⟩-ν r) = ?
    l1 n .(ν (ν swapₛₛ 0 1 qs)) .(ν (ν qs)) (ν-swap` qs) = ?
    l1 n .(ν sucₛₛ b 0) b (ν-elim` .b) = ?
    l1 n .(ν (zs ∪ sucₛₛ qs 0)) .(ν zs ∪ qs) (ν-∪` qs zs) = ?
    l1 n .(ν (zs · sucₛₛ qs 0)) .(ν zs · qs) (ν-·` qs zs) = ?
    l1 n .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = ?
    l1 n .(b ∪ 0b) b (rid .b) = ?
    l1 n .(x ∪ y) .(y ∪ x) (comm x y) = ?
    l1 n .(b ∪ b) b (idem .b) = ?
    l1 n .(x · y · z) .((x · y) · z) (assoc· x y z) = ?
    l1 n .(b · 1b) b (rid· .b) = ?
    l1 n .(x · y) .(y · x) (comm· x y) = ?
    l1 n .(x · 0b) .0b (def∅· x) = ?
    l1 n .(x · (y ∪ z)) .(x · y ∪ x · z) (dist x y z) = ?
    l1 n a .a (refl` .a) = ?
    l1 n a b (sym` .b .a r) = ?
    l1 n a b (trans` .a y .b r r₁) = ?
    l1 n a b (squash¹ .a .b r r₁ i) = ?


--   sucₛ : ∀ n → State → State
--   sucₛ n ⟨ x ⟩ₛ = ⟨ sucₛₛ x n ⟩ₛ
--   sucₛ n (⟨⟩-∪ x x₁ i) = ⟨⟩-∪ (cong (sucₛ n) x) (cong (sucₛ n) x₁) i
--   sucₛ n (⟨⟩-· x x₁ i) = ⟨⟩-· (cong (sucₛ n) x) (cong (sucₛ n) x₁) i
--   sucₛ n (⟨⟩-ν x i) = ⟨⟩-ν (cong (sucₛ (suc n)) x) i
--   sucₛ n (ν-swap` qs i) = ((cong (λ x → ⟨ ν (ν x) ⟩ₛ) (sucₛₛ-swapₛₛ (2 + n) 0 1 tt tt qs)) ∙ ν-swap` (sucₛₛ qs (2 + n))) i
--   sucₛ n (ν-elim` qs i) = (cong (λ a → ⟨ ν a ⟩ₛ) (sucₛₛ-sucₛₛ n 0 tt qs) ∙ ν-elim` (sucₛₛ qs n)) i
--   sucₛ n (ν-∪` qs zs i) = (cong (λ a → ⟨ ν (sucₛₛ zs (suc n) ∪ a) ⟩ₛ) (sucₛₛ-sucₛₛ n 0 tt qs) ∙ ν-∪` (sucₛₛ qs n) (sucₛₛ zs (suc n))) i
--   sucₛ n (ν-·` qs zs i) = (cong (λ a → ⟨ ν (sucₛₛ zs (suc n) · a) ⟩ₛ) (sucₛₛ-sucₛₛ n 0 tt qs) ∙ ν-·` (sucₛₛ qs n) (sucₛₛ zs (suc n))) i
--   sucₛ n (assoc x y z i) = assoc (sucₛₛ x n) (sucₛₛ y n) (sucₛₛ z n) i
--   sucₛ n (rid x i) = rid (sucₛₛ x n) i
--   sucₛ n (comm x y i) = comm (sucₛₛ x n) (sucₛₛ y n) i
--   sucₛ n (idem x i) = idem (sucₛₛ x n) i
--   sucₛ n (assoc· x y z i) = assoc· (sucₛₛ x n) (sucₛₛ y n) (sucₛₛ z n) i
--   sucₛ n (rid· x i) = rid· (sucₛₛ x n) i
--   sucₛ n (comm· x y i) = comm· (sucₛₛ x n) (sucₛₛ y n) i
--   sucₛ n (def∅· x i) = def∅· (sucₛₛ x n) i
--   sucₛ n (dist x y z i) = dist (sucₛₛ x n) (sucₛₛ y n) (sucₛₛ z n) i
--   sucₛ n (squash/ a b p1 p2 i j) = squash/ (sucₛ n a) (sucₛ n b) (cong (sucₛ n) p1) (cong (sucₛ n) p2) i j


--   swapₛ : ∀ n m → State → State
--   swapₛ n m ⟨ q ⟩ₛ = ⟨ swapₛₛ n m q ⟩ₛ
--   swapₛ n m (⟨⟩-∪ x x₁ i) = ⟨⟩-∪ (cong (swapₛ n m) x) (cong (swapₛ n m) x₁) i
--   swapₛ n m (⟨⟩-· x x₁ i) = ⟨⟩-· (cong (swapₛ n m) x) (cong (swapₛ n m) x₁) i
--   swapₛ n m (⟨⟩-ν q i) = ⟨⟩-ν (cong (swapₛ (suc n) (suc m)) q) i
--   swapₛ n m (ν-swap` qs i) = (cong (λ a → ⟨ ν ν a ⟩ₛ) (swapₛₛ-swapₛₛ (2 + n) (2 + m) 0 1 snotz (snotz ∘ injSuc) snotz (snotz ∘ injSuc) qs) ∙ ν-swap` (swapₛₛ (2 + n) (2 + m) qs)) i
--   swapₛ n m (ν-elim` qs i) = (cong (λ a → ⟨ ν a ⟩ₛ) (sym (sucₛₛ-swapₛₛ> 0 n m tt tt qs)) ∙ ν-elim` (swapₛₛ n m qs)) i
--   swapₛ n m (ν-∪` qs zs i) = (cong (λ a → ⟨ ν (swapₛₛ (suc n) (suc m) zs ∪ a) ⟩ₛ) (sym (sucₛₛ-swapₛₛ> 0 n m tt tt qs)) ∙ ν-∪` (swapₛₛ n m qs) (swapₛₛ (suc n) (suc m) zs)) i
--   swapₛ n m (ν-·` qs zs i) = (cong (λ a → ⟨ ν (swapₛₛ (suc n) (suc m) zs · a) ⟩ₛ) (sym (sucₛₛ-swapₛₛ> 0 n m tt tt qs)) ∙ ν-·` (swapₛₛ n m qs) (swapₛₛ (suc n) (suc m) zs)) i
--   swapₛ n m (assoc x y z i) = assoc (swapₛₛ n m x) (swapₛₛ n m y) (swapₛₛ n m z) i
--   swapₛ n m (rid x i) = rid (swapₛₛ n m x) i
--   swapₛ n m (comm x y i) = comm (swapₛₛ n m x) (swapₛₛ n m y) i
--   swapₛ n m (idem x i) = idem (swapₛₛ n m x) i
--   swapₛ n m (assoc· x y z i) = assoc· (swapₛₛ n m x) (swapₛₛ n m y) (swapₛₛ n m z) i
--   swapₛ n m (rid· x i) = rid· (swapₛₛ n m x) i
--   swapₛ n m (comm· x y i) = comm· (swapₛₛ n m x) (swapₛₛ n m y) i
--   swapₛ n m (def∅· x i) = def∅· (swapₛₛ n m x) i
--   swapₛ n m (dist x y z i) = dist (swapₛₛ n m x) (swapₛₛ n m y) (swapₛₛ n m z) i
--   swapₛ n m (squash/ a b p1 p2 i j) = squash/ (swapₛ n m a) (swapₛ n m b) (cong (swapₛ n m) p1) (cong (swapₛ n m) p2) i j


--   WellScopedₛ : State → ℕ → Type ℓ
--   WellScopedₛ ⟨ x ⟩ₛ n = WellScopedₛₛ x n
--   WellScopedₛ (⟨⟩-∪ x x₁ i) n = {!!}
--   WellScopedₛ (⟨⟩-· x x₁ i) n = {!!}
--   WellScopedₛ (⟨⟩-ν x i) n = {!!}
--   WellScopedₛ (ν-swap` qs i) n = {!!}
--   WellScopedₛ (ν-elim` qs i) n = {!!}
--   WellScopedₛ (ν-∪` qs zs i) n = {!!}
--   WellScopedₛ (ν-·` qs zs i) n = {!!}
--   WellScopedₛ (assoc x y z i) n = {!!}
--   WellScopedₛ (rid x i) n = {!!}
--   WellScopedₛ (comm x y i) n = {!!}
--   WellScopedₛ (idem x i) n = {!!}
--   WellScopedₛ (assoc· x y z i) n = {!!}
--   WellScopedₛ (rid· x i) n = {!!}
--   WellScopedₛ (comm· x y i) n = {!!}
--   WellScopedₛ (def∅· x i) n = {!!}
--   WellScopedₛ (dist x y z i) n = {!!}
--   WellScopedₛ (squash/ s s₁ x y i i₁) n = {!!}



-- --   AllisProp` : ∀{e ls k} → isProp (All {e} ls k)
-- --   AllisProp` {ls = []} = isPropUnit
-- --   AllisProp` {ls = x ∷ ls} {k} = isProp× (O.isProp≤ {suc x} {k}) AllisProp`
  
-- -- --   WSisProp` : (s : SState) → ∀ k → isProp (WellScoped s k)
-- -- --   WSisProp` ⟨ 0bₛ ⟩ₛ k = isPropUnit
-- -- --   WSisProp` ⟨ 1bₛ ⟩ₛ k = isPropUnit
-- -- --   WSisProp` ⟨ `[ ls ]ₛ c ⟩ₛ k = AllisProp` {_} {ls} {k}
-- -- --   WSisProp` ⟨ s₁ ∪ₛ s₂ ⟩ₛ k = isProp× (WSisProp` ⟨ s₁ ⟩ₛ k) (WSisProp` ⟨ s₂ ⟩ₛ k)
-- -- --   WSisProp` ⟨ s₁ ·ₛ s₂ ⟩ₛ k = isProp× (WSisProp` ⟨ s₁ ⟩ₛ k) (WSisProp` ⟨ s₂ ⟩ₛ k)
-- -- --   WSisProp` ⟨ νₛ s₁ ⟩ₛ k = WSisProp` ⟨ s₁ ⟩ₛ (suc k)

-- -- --   WSisProp : (s : SState) → isProp (∀ k → WellScoped s k)
-- -- --   WSisProp s = isPropΠ (WSisProp` s)



-- -- -- module _ {ℓ1} {ℓ2} {C1 : ∀ k → Type ℓ1} {C2 : ∀ k → Type ℓ2} where

-- -- --   module St1 = State C1
-- -- --   module St2 = State C2

-- -- --   mutual

-- -- --     {-# TERMINATING #-}
-- -- --     mapₛ : (∀{k} → C1 k → C2 k) → St1.State → St2.State
-- -- --     mapₛ f St1.0b = St2.0b
-- -- --     mapₛ f St1.1b = St2.1b
-- -- --     mapₛ f (State.`[ ls ] x) = St2.`[ ls ] f x
-- -- --     mapₛ f (x St1.∪ x₁) = mapₛ f x St2.∪ mapₛ f x₁
-- -- --     mapₛ f (x St1.· x₁) = mapₛ f x St2.· mapₛ f x₁
-- -- --     mapₛ f (St1.ν x) = St2.ν mapₛ f x
-- -- --     mapₛ f (St1.ν-elim x i) = ((cong St2.ν_ (mapₛ-suc {0} f x)) ∙ St2.ν-elim (mapₛ f x)) i
-- -- --     mapₛ f (St1.ν-∪ x x₁ i) = (cong (λ w → St2.ν (mapₛ f x St2.∪ w)) (mapₛ-suc {0} f x₁) ∙ St2.ν-∪ (mapₛ f x) (mapₛ f x₁)) i
-- -- --     mapₛ f (St1.ν-· x x₁ i) = (cong (λ w → St2.ν (mapₛ f x St2.· w)) (mapₛ-suc {0} f x₁) ∙ St2.ν-· (mapₛ f x) (mapₛ f x₁)) i
-- -- --     mapₛ f (St1.squash/ a b p1 p2 i j) = isOfHLevel→isOfHLevelDep 2 (λ a₁ → St2.squash/)  (mapₛ f a) (mapₛ f b) (cong (mapₛ f) p1) (cong (mapₛ f) p2) (St1.squash/ a b p1 p2) i j
-- -- --     mapₛ f (St1.assoc x x₁ x₂ i) = St2.assoc (mapₛ f x) (mapₛ f x₁) (mapₛ f x₂) i
-- -- --     mapₛ f (St1.rid x i) = St2.rid (mapₛ f x) i
-- -- --     mapₛ f (St1.comm x x₁ i) = St2.comm (mapₛ f x) (mapₛ f x₁) i
-- -- --     mapₛ f (St1.idem x i) = St2.idem (mapₛ f x) i
-- -- --     mapₛ f (St1.assoc· x x₁ x₂ i) = St2.assoc· (mapₛ f x) (mapₛ f x₁) (mapₛ f x₂) i
-- -- --     mapₛ f (St1.rid· x i) = St2.rid· (mapₛ f x) i
-- -- --     mapₛ f (St1.comm· x x₁ i) = St2.comm· (mapₛ f x) (mapₛ f x₁) i
-- -- --     mapₛ f (St1.def∅· x i) = St2.def∅· (mapₛ f x) i
-- -- --     mapₛ f (St1.dist x x₁ x₂ i) = St2.dist (mapₛ f x) (mapₛ f x₁) (mapₛ f x₂) i

-- -- --     mapₛ-suc : ∀ {n} → (f : ∀{k} → C1 k → C2 k) → ∀ x → mapₛ f (St1.sucₛ n x) ≡ St2.sucₛ n (mapₛ f x)
-- -- --     mapₛ-suc {n} f x = St1.elimProp {B = λ x → (n : ℕ) → mapₛ f (St1.sucₛ n x) ≡ St2.sucₛ n (mapₛ f x)}
-- -- --                            (λ a b i n → St2.squash/ _ _ (a n) (b n) i )
-- -- --                            (λ _ → refl)
-- -- --                            (λ _ → refl)
-- -- --                            (λ { ls x → (λ _ → refl) })
-- -- --                            (λ x x₁ → λ n → cong₂ St2._∪_ (x n) (x₁ n))
-- -- --                            (λ x x₁ → λ n → cong₂ St2._·_ (x n) (x₁ n))
-- -- --                            (λ x → λ n → cong St2.ν_ (x (suc n)))
-- -- --                            x n


-- -- --   mapₛ-StrSt : {s : St1.State} → (f : ∀{k} → C1 k → C2 k) → St1.IsStrSt s → St2.IsStrSt (mapₛ f s)
-- -- --   mapₛ-StrSt f St1.0bₛ = St2.0bₛ
-- -- --   mapₛ-StrSt f St1.1bₛ = St2.1bₛ
-- -- --   mapₛ-StrSt f (St1.`[_]ₛ_ _ _) = St2.`[_]ₛ_ _ _
-- -- --   mapₛ-StrSt f (St1._∪ₛ_ x x₁) = St2._∪ₛ_ (mapₛ-StrSt f x) (mapₛ-StrSt f x₁)
-- -- --   mapₛ-StrSt f (St1._·ₛ_ x x₁) = St2._·ₛ_ (mapₛ-StrSt f x) (mapₛ-StrSt f x₁)
-- -- --   mapₛ-StrSt f (St1.νₛ_ x) = St2.νₛ_ (mapₛ-StrSt f x)
