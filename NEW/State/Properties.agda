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

  l1 : ∀ {fv} {k} (vs : Vec {ℓ-zero} (Fin fv) k)
       n (nrl : n O.< suc fv) →
     _≡_ {ℓ-zero}
     {Vec {ℓ-zero}
      (Σ {ℓ-zero} {ℓ-zero} ℕ
       (λ k₁ →
          Σ {ℓ-zero} {ℓ-zero} ℕ
          (λ k₂ → _≡_ {ℓ-zero} {ℕ} (k₂ + suc k₁) (suc (suc fv)))))
      (suc (suc k))}
     (sbext {suc fv} {suc (suc fv)} {suc k} (0 ⦃ tt ⦄)
      (sbext {fv} {suc fv} {k} n vs (λ x → suc<?Fin {fv} x n) (n , nrl))
      (fsuc {suc fv}) (0 ⦃ tt ⦄))
     (sbext {suc fv} {suc (suc fv)} {suc k}
      (fst (fsuc {suc fv} (n , nrl)))
      (sbext {fv} {suc fv} {k} (0 ⦃ tt ⦄) vs (fsuc {fv}) (0 ⦃ tt ⦄))
      (λ x → suc<?Fin {suc fv} x (fst (fsuc {suc fv} (n , nrl))))
      (fsuc {suc fv} (n , nrl)))
  l1 [] zero nrl = refl
  l1 {fv = fv} {k = suc k} (x ∷ vs) zero nrl = λ i → f (l2 vs i) where
    f : Vec (Fin (suc (suc fv))) k → Vec (Fin (suc (suc fv))) (suc (suc (suc k)))
    f a = fzero ∷ fsuc (zero , nrl) ∷ fsuc (suc<?Fin x zero) ∷ a
    l2 : ∀{fv k} → (vs : Vec (Fin fv) k) → V.map fsuc (V.map (λ x₁ → suc<?Fin x₁ zero) vs) ≡ V.map (λ x₁ → suc<?Fin x₁ (fst (fsuc (zero , nrl)))) (V.map fsuc vs)
    l2 [] = refl
    l2 {fv} {suc k} (x ∷ vs) = λ i → f2 (l2 vs i) where
      f2 : Vec (Fin (suc (suc fv))) k → Vec (Fin (suc (suc fv))) (suc k)
      f2 a = fsuc (fsuc x) ∷ a
  
  l1 [] (suc n) nrl = refl
  l1 {fv} {suc k} (x ∷ vs) (suc n) nrl = {!!} where
    f3 : Vec (Fin (suc (suc fv))) (suc k) → Vec (Fin (suc (suc fv))) (suc (suc (suc k)))
    f3 a = fzero ∷ fsuc (suc<?Fin x (suc n)) ∷ a
    l3 : V.map fsuc (sbext n vs (λ x₁ → suc<?Fin x₁ (suc n)) (suc n , nrl)) ≡
         sbext n (V.map fsuc vs) (λ x₁ → suc<?Fin x₁ (fst (fsuc (suc n , nrl)))) (fsuc (suc n , nrl))
    l3 = {!!}



  l6 : ∀{k fv} → (vs : Vec (Fin fv) k) → ∀ n → (nrl : n O.< suc fv) →
      _≡_ {A = Vec (Fin (suc fv)) (suc k)} 
      (sbext n vs (λ x → suc<?Fin x n) (n , nrl))
      (sbext n vs (λ x → suc<?Fin x (fst (fsuc (n , nrl))))
      (fsuc (n , nrl)))
  l6 vs zero nrl = ?
  l6 vs (suc n) nrl = {!!}

  l7 : ∀{k fv} → (vs : Vec (Fin fv) k) → ∀ n → (nrl : n O.< suc fv) →
      _≡_ {A = Vec (Fin (suc (suc fv))) (suc (suc k))} (fzero {suc fv} ∷
      V.map fsuc (sbext n vs (λ x → suc<?Fin x n) (n , nrl)))
      (suc<?Fin fzero (fst (fsuc (n , nrl))) ∷
      sbext n (V.map fsuc vs) (λ x → suc<?Fin x (fst (fsuc (n , nrl))))
      (fsuc (n , nrl)))
  l7 vs n nrl = cong₂ V._∷_ (Σ≡Prop (λ _ → O.isProp≤) refl) (l6 vs n nrl)


  subst-sucₛₛ : ∀{fv k} → (vs : Vec (Fin fv) k)
                → (q : SState k) → (n : Fin (suc fv)) → substₛₛ (sbext (fst n) vs (λ x → suc<?Fin x (fst n)) n) (sucₛₛ q (fst n)) ≡ sucₛₛ (substₛₛ vs q) (fst n)
  subst-sucₛₛ vs 0b n = refl
  subst-sucₛₛ vs 1b n = refl
  subst-sucₛₛ vs (` [ secr ] c) n = cong (λ a → ` [ a ] c) (sbst-suc2 vs secr n)
  subst-sucₛₛ vs (q ∪ q₁) n = cong₂ _∪_ (subst-sucₛₛ vs q n) (subst-sucₛₛ vs q₁ n)
  subst-sucₛₛ vs (q · q₁) n = cong₂ _·_ (subst-sucₛₛ vs q n) (subst-sucₛₛ vs q₁ n)
  subst-sucₛₛ {fv} vs (ν q) fn@(n , nrl) = cong ν_ (cong (λ a → substₛₛ a (sucₛₛ q (suc n))) (l7 vs n nrl)  ∙ subst-sucₛₛ (sbext 0 vs fsuc 0) q (fsuc fn) )

  l2 : ∀ {fv} {k} (vs : Vec (Fin fv) k) {l}
       (secr : Vec (Fin k) l) (c : C l) →
       (ν (` [ sbst (sbext 0 vs fsuc 0) (lsuc<?Fin secr 0) ] c)) R substₛₛ vs (` [ secr ] c)
  l2 vs secr c = J (λ y eq → (ν (` [ y ] c)) R (substₛₛ vs (` [ secr ] c))) (ν-elim` (` [ sbst vs secr ] c)) (sym (sbst-suc vs secr))


--   substₛ : ∀{fv k} → Vec (Fin fv) k → State k → State fv
--   substₛ vs q = SQ.rec squash/ (λ e → ⟨ substₛₛ vs e ⟩ₛ) (λ a b r → eq/ (substₛₛ vs a) (substₛₛ vs b) (l1 vs a b r)) q where
--     l1 : ∀ {fv} {k} (vs : Vec (Fin fv) k)
--          (a b : SState k) (r : a R b) → substₛₛ vs a R substₛₛ vs b
--     l1 vs .(_ ∪ _) .(_ ∪ _) (⟨⟩-∪ r r₁) = ⟨⟩-∪ (l1 vs _ _ r) (l1 vs _ _ r₁)
--     l1 vs .(_ · _) .(_ · _) (⟨⟩-· r r₁) = ⟨⟩-· (l1 vs _ _ r) (l1 vs _ _ r₁)
--     l1 vs .(ν _) .(ν _) (⟨⟩-ν r) = ⟨⟩-ν (l1 _ _ _ r)
--     l1 vs .(ν (ν swapₛₛ 0 1 qs)) .(ν (ν qs)) (State.ν-swap` qs) = {!!}
--     l1 vs .(ν sucₛₛ b 0) b (ν-elim` .b) = J (λ y eq → (ν y) R substₛₛ vs b) (ν-elim` (substₛₛ vs b)) (sym (subst-sucₛₛ vs b 0))
--     -- substₛₛ (sbext 0 vs fsuc 0) vs (sucₛₛ b 0)
--     l1 vs .(ν (zs ∪ qs)) .(ν zs ∪ ν qs) (State.ν-∪` qs zs) = {!!}
--     l1 vs .(ν (zs · sucₛₛ qs 0)) .(ν zs · qs) (State.ν-·` qs zs) = {!!}
--     l1 vs .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (State.assoc x y z) = {!!}
--     l1 vs .(b ∪ 0b) b (State.rid .b) = {!!}
--     l1 vs .(x ∪ y) .(y ∪ x) (State.comm x y) = {!!}
--     l1 vs .(b ∪ b) b (State.idem .b) = {!!}
--     l1 vs .(x · y · z) .((x · y) · z) (State.assoc· x y z) = {!!}
--     l1 vs .(b · 1b) b (State.rid· .b) = {!!}
--     l1 vs .(x · y) .(y · x) (State.comm· x y) = {!!}
--     l1 vs .(x · 0b) .0b (State.def∅· x) = {!!}
--     l1 vs .(x · (y ∪ z)) .(x · y ∪ x · z) (State.dist x y z) = {!!}
--     l1 vs a .a (State.refl` .a) = {!!}
--     l1 vs a b (State.sym` .b .a r) = {!!}
--     l1 vs a b (State.trans` .a y .b r r₁) = {!!}
--     l1 vs a b (State.squash₁ .a .b r r₁ i) = {!!}



-- module _ {ℓ1} {ℓ2} {C1 : ∀ k → Type ℓ1} {C2 : ∀ k → Type ℓ2} where

--   module S1 = State C1
--   module S2 = State C2

--   open S2

--   mapₛₛ : ∀{fv} → (∀{k} → C1 k → C2 k) → (q : S1.SState fv) → S2.SState fv
--   mapₛₛ f 0b = 0b
--   mapₛₛ f 1b = 1b
--   mapₛₛ f (` [ secr ] c) = ` [ secr ] (f c)
--   mapₛₛ f (lq ∪ rq) = mapₛₛ f lq ∪ mapₛₛ f rq 
--   mapₛₛ f (lq · rq) = mapₛₛ f lq · mapₛₛ f rq 
--   mapₛₛ f (ν q) = ν mapₛₛ f q

--   -- mapₛ : (∀{k} → C1 k → C2 k) → S1.State → S2.State
--   -- mapₛ f q = SQ.rec squash/ (λ x → ⟨ mapₛₛ f x ⟩ₛ) (λ a b r → eq/ _ _ (l1 a b r)) q where
--   --   l1 : (a b : S1.SState) →
--   --    a S1.R b → (mapₛₛ f a) R (mapₛₛ f b)
--   --   l1 .(_ S1.∪ _) .(_ S1.∪ _) (⟨⟩-∪ x x₁) = ⟨⟩-∪ (l1 _ _ x) (l1 _ _ x₁)
--   --   l1 .(_ S1.· _) .(_ S1.· _) (⟨⟩-· x x₁) = ⟨⟩-· (l1 _ _ x) (l1 _ _ x₁)
--   --   l1 .(S1.ν _) .(S1.ν _) (⟨⟩-ν x) = ⟨⟩-ν (l1 _ _ x)
--   --   l1 .(S1.ν (S1.ν S1.swapₛₛ 0 1 qs)) .(S1.ν (S1.ν qs)) (ν-swap` qs) = {!!}
--   --   l1 .(S1.ν S1.sucₛₛ b 0) b (S1.ν-elim` .b) = {!!}
--   --   l1 .(S1.ν (zs S1.∪ S1.sucₛₛ qs 0)) .(S1.ν zs S1.∪ qs) (S1.ν-∪` qs zs) = {!!}
--   --   -- l1 .(ν (zs · sucₛₛ qs 0)) .(ν zs · qs) (ν-·` qs zs) = ?
--   --   -- l1 .(x ∪ y ∪ z) .((x ∪ y) ∪ z) (assoc x y z) = ?
--   --   -- l1 .(b ∪ 0b) b (rid .b) = ?
--   --   -- l1 .(x ∪ y) .(y ∪ x) (comm x y) = ?
--   --   -- l1 .(b ∪ b) b (idem .b) = ?
--   --   -- l1 .(x · y · z) .((x · y) · z) (assoc· x y z) = ?
--   --   -- l1 .(b · 1b) b (rid· .b) = ?
--   --   -- l1 .(x · y) .(y · x) (comm· x y) = ?
--   --   -- l1 .(x · 0b) .0b (def∅· x) = ?
--   --   -- l1 .(x · (y ∪ z)) .(x · y ∪ x · z) (dist x y z) = ?
--   --   -- l1 a .a (refl` .a) = ?
--   --   -- l1 a b (sym` .b .a x) = ?
--   --   -- l1 a b (trans` .a y .b x x₁) = ?
--   --   -- l1 a b (squash₁ .a .b x x₁ i) = ?

