{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Sum
open import Cubical.Data.Fin
import Cubical.Data.FinData as FD
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Vec as V
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Unit
import Cubical.Data.Nat.Order as O
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.HITs.SetQuotients as SQ renaming ([_] to ⟨_⟩ₛ)
open import Cubical.HITs.PropositionalTruncation

import State
open import State.Lemma

module State.Properties where

module _ {ℓ} {C : ∀ k → Type ℓ} where

  open State C

  sucₛₛ-sucₛₛ :  ∀{fv} → ∀ n m → m ≤ n → (q : SState fv) → sucₛₛ (sucₛₛ q m) (suc n) ≡ sucₛₛ (sucₛₛ q n) m 
  sucₛₛ-sucₛₛ n m m≤n 0b = refl
  sucₛₛ-sucₛₛ n m m≤n 1b = refl
  sucₛₛ-sucₛₛ n m m≤n (` [ secr ] c) = cong (λ vs → ` [ vs ] c) (lsuc-lsuc-Fin n m m≤n secr)
  sucₛₛ-sucₛₛ n m m≤n (q ∪ q₁) = cong₂ _∪_ (sucₛₛ-sucₛₛ n m m≤n q) (sucₛₛ-sucₛₛ n m m≤n q₁)
  sucₛₛ-sucₛₛ n m m≤n (q · q₁) = cong₂ _·_ (sucₛₛ-sucₛₛ n m m≤n q) (sucₛₛ-sucₛₛ n m m≤n q₁)
  sucₛₛ-sucₛₛ n m m≤n (ν q) = cong ν_ (sucₛₛ-sucₛₛ (suc n) (suc m) m≤n q)

  sucₛₛ-swapₛₛ : ∀{fv} → ∀ t m e → fst m < t → fst e < t → (q : SState fv) → sucₛₛ (swapₛₛ m e q) t ≡ swapₛₛ (fext m) (fext e) (sucₛₛ q t)
  sucₛₛ-swapₛₛ t m e m<t e<t 0b = refl
  sucₛₛ-swapₛₛ t m e m<t e<t 1b = refl
  sucₛₛ-swapₛₛ t m e m<t e<t (` [ secr ] c) = cong (λ vs → ` ([ vs ] c)) (lsuc-lswap-Fin t m e m<t e<t secr)
  sucₛₛ-swapₛₛ t m e m<t e<t (q ∪ q₁) = cong₂ _∪_ (sucₛₛ-swapₛₛ t m e m<t e<t q)  (sucₛₛ-swapₛₛ t m e m<t e<t q₁)
  sucₛₛ-swapₛₛ t m e m<t e<t (q · q₁) = cong₂ _·_ (sucₛₛ-swapₛₛ t m e m<t e<t q) (sucₛₛ-swapₛₛ t m e m<t e<t q₁)
  sucₛₛ-swapₛₛ t m e m<t e<t (ν q) = cong ν_ (sucₛₛ-swapₛₛ (suc t) (fsuc m) (fsuc e) m<t e<t q)

  sucₛₛ-swapₛₛ> : ∀{fv} → ∀ t m e → t ≤ fst m → t ≤ fst e → (q : SState fv) → sucₛₛ (swapₛₛ m e q) t ≡ swapₛₛ (fsuc m) (fsuc e) (sucₛₛ q t)
  sucₛₛ-swapₛₛ> t m e m>t e>t 0b = refl
  sucₛₛ-swapₛₛ> t m e m>t e>t 1b = refl
  sucₛₛ-swapₛₛ> t m e m>t e>t (` [ secr ] c) = cong (λ vs → ` ([ vs ] c)) (lsuc-lswap>-Fin t m e m>t e>t secr)
  sucₛₛ-swapₛₛ> t m e m>t e>t (q ∪ q₁) = cong₂ _∪_ (sucₛₛ-swapₛₛ> t m e m>t e>t q)  (sucₛₛ-swapₛₛ> t m e m>t e>t q₁)
  sucₛₛ-swapₛₛ> t m e m>t e>t (q · q₁) = cong₂ _·_ (sucₛₛ-swapₛₛ> t m e m>t e>t q) (sucₛₛ-swapₛₛ> t m e m>t e>t q₁)
  sucₛₛ-swapₛₛ> t m e m>t e>t (ν q) = cong ν_ (sucₛₛ-swapₛₛ> (suc t) (fsuc m) (fsuc e) m>t e>t q)



  swapₛₛ-swapₛₛ : ∀{fv} → ∀ t1 t2 e1 e2 → ¬ (t1 ≡ e1) → ¬ (t1 ≡ e2) →  ¬ (t2 ≡ e1) → ¬ (t2 ≡ e2) → (q : SState fv)
                → swapₛₛ t1 t2 (swapₛₛ e1 e2 q) ≡ swapₛₛ e1 e2 (swapₛₛ t1 t2 q)
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 0b = refl
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 1b = refl
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 (` [ secr ] c) = cong (λ vs → ` ([ vs ] c)) (lswap-lswap-Fin t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 secr)
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 (q ∪ q₁) = cong₂ _∪_ (swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 q) (swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 q₁)
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 (q · q₁) = cong₂ _·_ (swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 q) (swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 q₁)
  swapₛₛ-swapₛₛ t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 (ν q) = cong ν_ (swapₛₛ-swapₛₛ (fsuc t1) (fsuc t2) (fsuc e1) (fsuc e2) (t1≢e1 ∘ λ a → Fin-fst-≡ (injSuc (fst (PathPΣ a)))) (t1≢e2 ∘ λ a → Fin-fst-≡ (injSuc (fst (PathPΣ a)))) (t2≢e1 ∘ λ a → Fin-fst-≡ (injSuc (fst (PathPΣ a)))) (t2≢e2 ∘ λ a → Fin-fst-≡ (injSuc (fst (PathPΣ a)))) q)


  _∪`_ : ∀{fv} (lq rq : State fv) → State fv
  _∪`_ {fv} lq rq = SQ.rec squash/ (λ lq → SQ.rec squash/ (λ rq → ⟨ lq ∪ rq ⟩ₛ) l1 rq) (l2 rq) lq where
    l1 : {lq : SState fv} (a b : SState fv) →
         a R b → ⟨ lq ∪ a ⟩ₛ ≡ ⟨ lq ∪ b ⟩ₛ
    l1 {lq} _ _ R1 = eq/ _ _ (⟨⟩-∪ (refl` _) R1)
    l2 : (rq : State fv) → (a b : SState fv) →
         a R b → 
         SQ.rec squash/ (λ rq → ⟨ a ∪ rq ⟩ₛ) l1 rq
         ≡
         SQ.rec squash/ (λ rq → ⟨ b ∪ rq ⟩ₛ) l1 rq
    l2 rq a b R1 = SQ.elimProp {P = λ z → SQ.rec squash/ (λ rq → ⟨ a ∪ rq ⟩ₛ) l1 z
         ≡
         SQ.rec squash/ (λ rq → ⟨ b ∪ rq ⟩ₛ) l1 z} (λ z → squash/ _ _) (λ rq → eq/ (a ∪ rq) (b ∪ rq) (⟨⟩-∪ R1 (refl` _))) rq 

  _·`_ : ∀{fv} → (lq rq : State fv) → State fv
  _·`_ {fv} lq rq = SQ.rec squash/ (λ lq → SQ.rec squash/ (λ rq → ⟨ lq · rq ⟩ₛ) l1 rq) (l2 rq) lq where
    l1 : {lq : SState fv} (a b : SState fv) →
         a R b → ⟨ lq · a ⟩ₛ ≡ ⟨ lq · b ⟩ₛ
    l1 {lq} _ _ R1 = eq/ _ _ (⟨⟩-· (refl` _) R1)
    l2 : (rq : State fv) → (a b : SState fv) →
         a R b → 
         SQ.rec squash/ (λ rq → ⟨ a · rq ⟩ₛ) l1 rq
         ≡
         SQ.rec squash/ (λ rq → ⟨ b · rq ⟩ₛ) l1 rq
    l2 rq a b R1 = SQ.elimProp {P = λ z → SQ.rec squash/ (λ rq → ⟨ a · rq ⟩ₛ) l1 z
         ≡
         SQ.rec squash/ (λ rq → ⟨ b · rq ⟩ₛ) l1 z} (λ z → squash/ _ _) (λ rq → eq/ (a · rq) (b · rq) (⟨⟩-· R1 (refl` _))) rq 

  ν`_ : ∀{fv} → (q : State (suc fv)) → State fv
  ν`_ {fv} q = SQ.rec squash/ (λ x → ⟨ ν x ⟩ₛ) l1 q where
    l1 : (a b : SState (suc fv)) → a R b → ⟨ ν a ⟩ₛ ≡ ⟨ ν b ⟩ₛ
    l1 a b R1 = eq/ _ _ (⟨⟩-ν R1)

  sucₛ : ∀{fv} → (n : ℕ) → State fv → State (suc fv)
  sucₛ {fv} n q = SQ.rec squash/ (λ a → ⟨ sucₛₛ a n ⟩ₛ) (λ a b r → eq/ _ _ (l1 n a b r)) q where
    l1 : ∀{fv} → (n : ℕ) → (a b : SState fv) → (r : a R b) → (sucₛₛ a n ) R ( sucₛₛ b n )
    l1 n .(_ ∪ _) .(_ ∪ _) (⟨⟩-∪ r r₁) = ⟨⟩-∪ (l1 n _ _ r) (l1 n _ _ r₁)
    l1 n .(_ · _) .(_ · _) (⟨⟩-· r r₁) = ⟨⟩-· (l1 n _ _ r) (l1 n _ _ r₁)
    l1 n .(ν _) .(ν _) (⟨⟩-ν r) = ⟨⟩-ν (l1 (suc n) _ _ r)
    l1 n .(ν (ν swapₛₛ 0 1 qs)) .(ν (ν qs)) (ν-swap` qs) = subst (λ x → (ν (ν x)) R (ν (ν sucₛₛ qs (suc (suc n))))) (sym (sucₛₛ-swapₛₛ (2 + n) 0 1 tt tt qs)) (ν-swap` (sucₛₛ qs (suc (suc n))))
    l1 n .(ν sucₛₛ qs 0) qs (ν-elim` .qs) = subst (λ a → (ν a) R (sucₛₛ qs n)) (sym (sucₛₛ-sucₛₛ n 0 tt qs)) (ν-elim` (sucₛₛ qs n))
    l1 n .(ν (zs ∪ qs)) .(ν zs ∪ ν qs) (ν-∪` qs zs) = ν-∪` (sucₛₛ qs (suc n)) (sucₛₛ zs (suc n))
    l1 n .(ν (zs · sucₛₛ qs 0)) .(ν zs · qs) (ν-·` qs zs) = subst (λ a → (ν (sucₛₛ zs (suc n) · a)) R (sucₛₛ (ν zs · qs) n)) (sym (sucₛₛ-sucₛₛ n 0 tt qs)) (ν-·` (sucₛₛ qs n) (sucₛₛ zs (suc n)))
    l1 n .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = assoc (sucₛₛ x n) (sucₛₛ y n) (sucₛₛ z n)
    l1 n .(b ∪ 0b) b (rid .b) = rid (sucₛₛ b n)
    l1 n .(x ∪ y) .(y ∪ x) (comm x y) = comm (sucₛₛ x n) (sucₛₛ y n)
    l1 n .(b ∪ b) b (idem .b) = idem (sucₛₛ b n)
    l1 n .(x · y · z) .((x · y) · z) (assoc· x y z) = assoc· (sucₛₛ x n) (sucₛₛ y n) (sucₛₛ z n)
    l1 n .(b · 1b) b (rid· .b) = rid· (sucₛₛ b n)
    l1 n .(x · y) .(y · x) (comm· x y) = comm· (sucₛₛ x n) (sucₛₛ y n)
    l1 n .(x · 0b) .0b (def∅· x) = def∅· (sucₛₛ x n)
    l1 n .(x · (y ∪ z)) .(x · y ∪ x · z) (dist x y z) = dist (sucₛₛ x n) (sucₛₛ y n) (sucₛₛ z n)
    l1 n a .a (refl` .a) = refl` (sucₛₛ a n)
    l1 n a b (sym` .b .a r) = sym` (sucₛₛ b n) (sucₛₛ a n) (l1 n b a r)
    l1 n a b (trans` .a y .b r r₁) = trans` (sucₛₛ a n) (sucₛₛ y n) (sucₛₛ b n) (l1 n a y r) (l1 n y b r₁)
    l1 n a b (squash₁ .a .b r r₁ i) = squash₁ (sucₛₛ a n) (sucₛₛ b n) (l1 n a b r) (l1 n a b r₁) i

  swapₛ : ∀{fv} → (n m : Fin fv) → State fv → State fv
  swapₛ {fv} n m q = SQ.rec squash/ (λ q → ⟨ swapₛₛ n m q ⟩ₛ) (λ _ _ r → eq/ _ _ (l1 n m _ _ r)) q where
    l1 : ∀{fv} → (n m : Fin fv) → (a b : SState fv) →
         a R b → (swapₛₛ n m a) R (swapₛₛ n m b)
    l1 n m .(_ ∪ _) .(_ ∪ _) (⟨⟩-∪ r r₁) = ⟨⟩-∪ (l1 n m _ _ r) (l1 n m _ _ r₁)
    l1 n m .(_ · _) .(_ · _) (⟨⟩-· r r₁) = ⟨⟩-· (l1 n m _ _ r) (l1 n m _ _ r₁)
    l1 n m .(ν _) .(ν _) (⟨⟩-ν r) = ⟨⟩-ν (l1 (fsuc n) (fsuc m) _ _ r)
    l1 n m .(ν (ν swapₛₛ 0 1 qs)) .(ν (ν qs)) (ν-swap` qs) = subst (λ a → (ν ν a ) R (swapₛₛ n m (ν (ν qs)))) (sym (swapₛₛ-swapₛₛ (fsuc (fsuc n)) (fsuc (fsuc m)) 0 1 (λ a → snotz (fst (PathPΣ a))) (λ a → (snotz ∘ injSuc) (fst (PathPΣ a))) (λ a → snotz (fst (PathPΣ a))) (λ a → (snotz ∘ injSuc) (fst (PathPΣ a))) qs)) (ν-swap` (swapₛₛ (fsuc (fsuc n)) (fsuc (fsuc m)) qs))
    l1 n m .(ν sucₛₛ b 0) b (ν-elim` .b) = subst (λ a → (ν a ) R (swapₛₛ n m b)) (sucₛₛ-swapₛₛ> 0 n m tt tt b) (ν-elim` (swapₛₛ n m b))
    l1 n m .(ν (zs ∪ qs)) .(ν zs ∪ ν qs) (ν-∪` qs zs) = ν-∪` (swapₛₛ (fsuc n) (fsuc m) qs) (swapₛₛ (fsuc n) (fsuc m) zs)
    l1 n m .(ν (zs · sucₛₛ qs 0)) .(ν zs · qs) (ν-·` qs zs) = subst (λ a → (ν (swapₛₛ (fsuc n) (fsuc m) zs · a)) R (swapₛₛ n m (ν zs · qs))) (sucₛₛ-swapₛₛ> 0 n m tt tt qs) (ν-·` (swapₛₛ n m qs) (swapₛₛ (fsuc n) (fsuc m) zs))
    l1 n m .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = assoc (swapₛₛ n m x) (swapₛₛ n m y) (swapₛₛ n m z)
    l1 n m .(b ∪ 0b) b (rid .b) = rid (swapₛₛ n m b)
    l1 n m .(x ∪ y) .(y ∪ x) (comm x y) = comm (swapₛₛ n m x) (swapₛₛ n m y)
    l1 n m .(b ∪ b) b (idem .b) = idem (swapₛₛ n m b)
    l1 n m .(x · y · z) .((x · y) · z) (assoc· x y z) = assoc· (swapₛₛ n m x) (swapₛₛ n m y) (swapₛₛ n m z)
    l1 n m .(b · 1b) b (rid· .b) = rid· (swapₛₛ n m b)
    l1 n m .(x · y) .(y · x) (comm· x y) = comm· (swapₛₛ n m x) (swapₛₛ n m y)
    l1 n m .(x · 0b) .0b (def∅· x) = def∅· (swapₛₛ n m x)
    l1 n m .(x · (y ∪ z)) .(x · y ∪ x · z) (dist x y z) = dist (swapₛₛ n m x) (swapₛₛ n m y) (swapₛₛ n m z)
    l1 n m a .a (refl` .a) = refl` (swapₛₛ n m a)
    l1 n m a b (sym` .b .a r) = sym` (swapₛₛ n m b) (swapₛₛ n m a) (l1 n m b a r)
    l1 n m a b (trans` .a y .b r r₁) = trans` (swapₛₛ n m a) (swapₛₛ n m y) (swapₛₛ n m b) (l1 n m a y r) (l1 n m y b r₁)
    l1 n m a b (squash₁ .a .b r r₁ i) = squash₁ (swapₛₛ n m a) (swapₛₛ n m b) (l1 n m a b r) (l1 n m a b r₁) i


module _ {ℓ} {C : ∀ k → Type ℓ} where

  open State C

  subst-swapₛₛ : ∀ {fv} {k} n (m t : Fin (suc (suc n) + k)) → (mrl : fst m ≤ suc n) → (trl : fst t ≤ suc n) → (vs : Vec (Fin fv) k) (q : SState (suc (suc n) + k)) →
                swapₛₛ (fst m , to-≤ (≤-trans {fst m} {suc n} {suc (n + fv)} mrl (k≤k+n n))) (fst t , to-≤ (≤-trans {fst t} {suc n} {suc (n + fv)} trl (k≤k+n n))) (substₛₛ (sbsuc (suc (suc n)) vs) q) ≡ substₛₛ (sbsuc (suc (suc n)) vs) (swapₛₛ m t q)
  subst-swapₛₛ n m t mrl trl vs 0b = refl
  subst-swapₛₛ n m t mrl trl vs 1b = refl
  subst-swapₛₛ n m t mrl trl vs (` [ secr ] c) = cong (λ a → ` [ a ] c) (sbst-swap n m t mrl trl vs secr)
  subst-swapₛₛ n m t mrl trl vs (q ∪ q₁) = cong₂ _∪_ (subst-swapₛₛ n m t mrl trl vs q) (subst-swapₛₛ n m t mrl trl vs q₁)
  subst-swapₛₛ n m t mrl trl vs (q · q₁) = cong₂ _·_ (subst-swapₛₛ n m t mrl trl vs q) (subst-swapₛₛ n m t mrl trl vs q₁)
  subst-swapₛₛ n m t mrl trl vs (ν q) = cong ν_ (subst-swapₛₛ (suc n) (fsuc m) (fsuc t) mrl trl vs q)



  subst-sucₛₛ : ∀ {fv} {k} n (vs : Vec (Fin fv) k) (q : SState (n + k)) →
                sucₛₛ (substₛₛ (sbsuc n vs) q) n ≡ substₛₛ (sbsuc (suc n) vs) (sucₛₛ q n)
  subst-sucₛₛ n vs 0b = refl
  subst-sucₛₛ n vs 1b = refl
  subst-sucₛₛ n vs (` [ secr ] c) = cong (λ s → ` [ s ] c) (sbst-suc n vs secr)
  subst-sucₛₛ n vs (q ∪ q₁) = cong₂ _∪_ (subst-sucₛₛ n vs q) (subst-sucₛₛ n vs q₁)
  subst-sucₛₛ n vs (q · q₁) = cong₂ _·_ (subst-sucₛₛ n vs q) (subst-sucₛₛ n vs q₁)
  subst-sucₛₛ n vs (ν q) = cong ν_ (subst-sucₛₛ (1 + n) vs q)


  substₛ : ∀{fv k} → Vec (Fin fv) k → State k → State fv
  substₛ vs q = SQ.rec squash/ (λ e → ⟨ substₛₛ vs e ⟩ₛ) (λ a b r → eq/ (substₛₛ vs a) (substₛₛ vs b) (l1 vs a b r)) q where
    l1 : ∀ {fv} {k} (vs : Vec (Fin fv) k)
         (a b : SState k) (r : a R b) → substₛₛ vs a R substₛₛ vs b
    l1 vs .(_ ∪ _) .(_ ∪ _) (⟨⟩-∪ r r₁) = ⟨⟩-∪ (l1 vs _ _ r) (l1 vs _ _ r₁)
    l1 vs .(_ · _) .(_ · _) (⟨⟩-· r r₁) = ⟨⟩-· (l1 vs _ _ r) (l1 vs _ _ r₁)
    l1 vs .(ν _) .(ν _) (⟨⟩-ν r) = ⟨⟩-ν (l1 _ _ _ r)
    l1 vs .(ν (ν swapₛₛ 0 1 qs)) .(ν (ν qs)) (ν-swap` qs) = subst (λ x → (ν (ν x)) R substₛₛ vs (ν (ν qs))) (subst-swapₛₛ 0 0 1 tt tt vs qs) (ν-swap` (substₛₛ (sbsuc (suc (suc 0)) vs) qs))
    l1 vs .(ν sucₛₛ b 0) b (ν-elim` .b) = subst (λ x → x) (cong (λ a → (ν a) R substₛₛ vs b) (subst-sucₛₛ 0 vs b)) (ν-elim` (substₛₛ vs b))
    l1 vs .(ν (zs ∪ qs)) .(ν zs ∪ ν qs) (ν-∪` qs zs) = ν-∪` (substₛₛ (sbsuc 1 vs) qs) (substₛₛ (sbsuc 1 vs) zs)
    l1 vs .(ν (zs · sucₛₛ qs 0)) .(ν zs · qs) (ν-·` qs zs) = subst (λ a → (ν ((substₛₛ (sbsuc 1 vs) zs) · a)) R substₛₛ vs (ν zs · qs)) (subst-sucₛₛ 0 vs qs) (ν-·` (substₛₛ vs qs) (substₛₛ (sbsuc 1 vs) zs))
    l1 vs .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = assoc (substₛₛ vs x) (substₛₛ vs y) (substₛₛ vs z)
    l1 vs .(b ∪ 0b) b (rid .b) = rid (substₛₛ vs b)
    l1 vs .(x ∪ y) .(y ∪ x) (comm x y) = comm (substₛₛ vs x) (substₛₛ vs y)
    l1 vs .(b ∪ b) b (idem .b) = idem (substₛₛ vs b)
    l1 vs .(x · y · z) .((x · y) · z) (assoc· x y z) = assoc· (substₛₛ vs x) (substₛₛ vs y) (substₛₛ vs z)
    l1 vs .(b · 1b) b (rid· .b) = rid· (substₛₛ vs b)
    l1 vs .(x · y) .(y · x) (comm· x y) = comm· (substₛₛ vs x) (substₛₛ vs y)
    l1 vs .(x · 0b) .0b (def∅· x) = def∅· (substₛₛ vs x)
    l1 vs .(x · (y ∪ z)) .(x · y ∪ x · z) (dist x y z) = dist (substₛₛ vs x) (substₛₛ vs y) (substₛₛ vs z)
    l1 vs a .a (refl` .a) = refl` (substₛₛ vs a)
    l1 vs a b (sym` .b .a r) = sym` (substₛₛ vs b) (substₛₛ vs a) (l1 vs b a r)
    l1 vs a b (trans` .a y .b r r₁) = trans` (substₛₛ vs a) (substₛₛ vs y) (substₛₛ vs b) (l1 vs a y r) (l1 vs y b r₁)
    l1 vs a b (squash₁ .a .b r r₁ i) = squash₁ (substₛₛ vs a) (substₛₛ vs b) (l1 vs a b r) (l1 vs a b r₁) i



module _ {ℓ1} {ℓ2} {C1 : ∀ k → Type ℓ1} {C2 : ∀ k → Type ℓ2} where

  module S1 = State C1
  module S2 = State C2

  open S2

  mapₛₛ : ∀{fv} → (∀{k} → C1 k → C2 k) → (q : S1.SState fv) → S2.SState fv
  mapₛₛ f 0b = 0b
  mapₛₛ f 1b = 1b
  mapₛₛ f (` [ secr ] c) = ` [ secr ] (f c)
  mapₛₛ f (lq ∪ rq) = mapₛₛ f lq ∪ mapₛₛ f rq 
  mapₛₛ f (lq · rq) = mapₛₛ f lq · mapₛₛ f rq 
  mapₛₛ f (ν q) = ν mapₛₛ f q

  -- mapₛ : (∀{k} → C1 k → C2 k) → S1.State → S2.State
  -- mapₛ f q = SQ.rec squash/ (λ x → ⟨ mapₛₛ f x ⟩ₛ) (λ a b r → eq/ _ _ (l1 a b r)) q where
  --   l1 : (a b : S1.SState) →
  --    a S1.R b → (mapₛₛ f a) R (mapₛₛ f b)
  --   l1 .(_ S1.∪ _) .(_ S1.∪ _) (⟨⟩-∪ x x₁) = ⟨⟩-∪ (l1 _ _ x) (l1 _ _ x₁)
  --   l1 .(_ S1.· _) .(_ S1.· _) (⟨⟩-· x x₁) = ⟨⟩-· (l1 _ _ x) (l1 _ _ x₁)
  --   l1 .(S1.ν _) .(S1.ν _) (⟨⟩-ν x) = ⟨⟩-ν (l1 _ _ x)
  --   l1 .(S1.ν (S1.ν S1.swapₛₛ 0 1 qs)) .(S1.ν (S1.ν qs)) (ν-swap` qs) = {!!}
  --   l1 .(S1.ν S1.sucₛₛ b 0) b (S1.ν-elim` .b) = {!!}
  --   l1 .(S1.ν (zs S1.∪ S1.sucₛₛ qs 0)) .(S1.ν zs S1.∪ qs) (S1.ν-∪` qs zs) = {!!}
  --   -- l1 .(ν (zs · sucₛₛ qs 0)) .(ν zs · qs) (ν-·` qs zs) = ?
  --   -- l1 .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = ?
  --   -- l1 .(b ∪ 0b) b (rid .b) = ?
  --   -- l1 .(x ∪ y) .(y ∪ x) (comm x y) = ?
  --   -- l1 .(b ∪ b) b (idem .b) = ?
  --   -- l1 .(x · y · z) .((x · y) · z) (assoc· x y z) = ?
  --   -- l1 .(b · 1b) b (rid· .b) = ?
  --   -- l1 .(x · y) .(y · x) (comm· x y) = ?
  --   -- l1 .(x · 0b) .0b (def∅· x) = ?
  --   -- l1 .(x · (y ∪ z)) .(x · y ∪ x · z) (dist x y z) = ?
  --   -- l1 a .a (refl` .a) = ?
  --   -- l1 a b (sym` .b .a x) = ?
  --   -- l1 a b (trans` .a y .b x x₁) = ?
  --   -- l1 a b (squash₁ .a .b x x₁ i) = ?

