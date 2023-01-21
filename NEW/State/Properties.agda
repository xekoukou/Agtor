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
open import Cubical.HITs.PropositionalTruncation

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

  sucₛ : (n : ℕ) → State → State
  sucₛ n q = SQ.elim (λ _ → squash/) (λ a → ⟨ sucₛₛ a n ⟩ₛ) (λ a b r → eq/ _ _ (l1 n a b r)) q where
    l1 : (n : ℕ) (a b : SState) (r : a R b) → (sucₛₛ a n ) R ( sucₛₛ b n )
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

  swapₛ : (n m : ℕ) → State → State
  swapₛ n m q = SQ.rec squash/ (λ q → ⟨ swapₛₛ n m q ⟩ₛ) (λ _ _ r → eq/ _ _ (l1 n m _ _ r)) q where
    l1 : ∀ n m → (a b : SState) →
         a R b → (swapₛₛ n m a) R (swapₛₛ n m b)
    l1 n m .(_ ∪ _) .(_ ∪ _) (⟨⟩-∪ r r₁) = ⟨⟩-∪ (l1 n m _ _ r) (l1 n m _ _ r₁)
    l1 n m .(_ · _) .(_ · _) (⟨⟩-· r r₁) = ⟨⟩-· (l1 n m _ _ r) (l1 n m _ _ r₁)
    l1 n m .(ν _) .(ν _) (⟨⟩-ν r) = ⟨⟩-ν (l1 (suc n) (suc m) _ _ r)
    l1 n m .(ν (ν swapₛₛ 0 1 qs)) .(ν (ν qs)) (ν-swap` qs) = subst (λ a → (ν ν a ) R (swapₛₛ n m (ν (ν qs)))) (sym (swapₛₛ-swapₛₛ (2 + n) (2 + m) 0 1 snotz (snotz ∘ injSuc) snotz (snotz ∘ injSuc) qs)) (ν-swap` (swapₛₛ (2 + n) (2 + m) qs))
    l1 n m .(ν sucₛₛ b 0) b (ν-elim` .b) = subst (λ a → (ν a ) R (swapₛₛ n m b)) (sucₛₛ-swapₛₛ> 0 n m tt tt b) (ν-elim` (swapₛₛ n m b))
    l1 n m .(ν (zs ∪ qs)) .(ν zs ∪ ν qs) (ν-∪` qs zs) = ν-∪` (swapₛₛ (suc n) (suc m) qs) (swapₛₛ (suc n) (suc m) zs)
    l1 n m .(ν (zs · sucₛₛ qs 0)) .(ν zs · qs) (ν-·` qs zs) = subst (λ a → (ν (swapₛₛ (suc n) (suc m) zs · a)) R (swapₛₛ n m (ν zs · qs))) (sucₛₛ-swapₛₛ> 0 n m tt tt qs) (ν-·` (swapₛₛ n m qs) (swapₛₛ (suc n) (suc m) zs))
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


  WellScopedₛ : (s : State) → (n : ℕ) → Type ℓ
  WellScopedₛ s n = ∃[ a ∈ SState ] (⟨ a ⟩ₛ ≡ s) × WellScopedₛₛ a n

  ws-swap : ∀ qs t r n → t < n → r < n → WellScopedₛₛ (swapₛₛ t r qs) n → WellScopedₛₛ qs n
  ws-swap 0b t r n t<n r<n ws-0b = ws-0b
  ws-swap 1b t r n t<n r<n ws-1g♭ = ws-1b
  ws-swap (` [ secr ] c) t r n t<n r<n (ws-` x) = ws-` (l2 secr x) where
    l2 : ∀{k} → (ls : Vec ℕ k) →  All< (lswap t r ls) n →  All< ls n
    l2 [] x = tt
    l2 (x ∷ ls) (swx<n , any) with t =? x
    ... | yes p = J (λ y eq → y < n) t<n p , l2 ls any
    ... | no ¬p with r =? x
    ... | yes p = J (λ y eq → y < n) r<n p , l2 ls any
    ... | no ¬p₁ = swx<n , l2 ls any

  ws-swap (qs ∪ qs₁) t r n t<n r<n (ws-∪ ws ws₁) = ws-∪ (ws-swap qs t r n t<n r<n ws) (ws-swap qs₁ t r n t<n r<n ws₁)
  ws-swap (qs · qs₁) t r n t<n r<n (ws-· ws ws₁) = ws-· (ws-swap qs t r n t<n r<n ws) (ws-swap qs₁ t r n t<n r<n ws₁)
  ws-swap (ν qs) t r n t<n r<n (ws-ν ws) = ws-ν (ws-swap qs (suc t) (suc r) (suc n) t<n r<n ws)

  ws-swap2 : ∀ qs t r n → t < n → r < n → WellScopedₛₛ qs n → WellScopedₛₛ (swapₛₛ t r qs) n
  ws-swap2 0b t r n t<n r<n ws-0b = ws-0b
  ws-swap2 1b t r n t<n r<n ws-1g♭ = ws-1b
  ws-swap2 (` [ secr ] c) t r n t<n r<n (ws-` x) = ws-` (l2 secr x) where
    l2 : ∀{k} → (ls : Vec ℕ k) →  All< ls n →  All< (lswap t r ls) n
    l2 [] x = tt
    l2 (x ∷ ls) (swx<n , any) with t =? x
    ... | yes p = r<n , l2 ls any
    ... | no ¬p with r =? x
    ... | yes p = t<n , l2 ls any
    ... | no ¬p₁ = swx<n , l2 ls any

  ws-swap2 (qs ∪ qs₁) t r n t<n r<n (ws-∪ ws ws₁) = ws-∪ (ws-swap2 qs t r n t<n r<n ws) (ws-swap2 qs₁ t r n t<n r<n ws₁)
  ws-swap2 (qs · qs₁) t r n t<n r<n (ws-· ws ws₁) = ws-· (ws-swap2 qs t r n t<n r<n ws) (ws-swap2 qs₁ t r n t<n r<n ws₁)
  ws-swap2 (ν qs) t r n t<n r<n (ws-ν ws) = ws-ν (ws-swap2 qs (suc t) (suc r) (suc n) t<n r<n ws)


  ws-suc : ∀ n r q → r ≤ n → WellScopedₛₛ (sucₛₛ q r) (suc n) → WellScopedₛₛ q n
  ws-suc n r 0b r≤n ws = ws-0b
  ws-suc n r 1b r≤n ws = ws-1b
  ws-suc n r (` [ secr ] c) r≤n (ws-` x) = ws-` (l4 secr x) where
    l4 : ∀{k} → (ls : Vec ℕ k) → All< (lsuc<? ls r) (suc n) → All< ls n
    l4 [] any = any
    l4 (x ∷ ls) (s<sn , any) = l5 s<sn , l4 ls any where
      l5 : suc<? x r < suc n → x < n
      l5 e with x <? r
      ... | yes p = ≤-trans {suc x} {r} {n} p r≤n
      ... | no ¬p = e
  ws-suc n r (q ∪ q₁) r≤n (ws-∪ ws ws₁) = ws-∪ (ws-suc n r q r≤n ws) (ws-suc n r q₁ r≤n ws₁)
  ws-suc n r (q · q₁) r≤n (ws-· ws ws₁) = ws-· (ws-suc n r q r≤n ws) (ws-suc n r q₁ r≤n ws₁)
  ws-suc n r (ν q) r≤n (ws-ν ws) = ws-ν (ws-suc (suc n) (suc r) q r≤n ws)


  ws-suc2 : ∀ n r q → r ≤ n → WellScopedₛₛ q n → WellScopedₛₛ (sucₛₛ q r) (suc n)
  ws-suc2 n r 0b r≤n ws = ws-0b
  ws-suc2 n r 1b r≤n ws = ws-1b
  ws-suc2 n r (` [ secr ] c) r≤n (ws-` x) = ws-` (l4 secr x) where
    l4 : ∀{k} → (ls : Vec ℕ k) → All< ls n → All< (lsuc<? ls r) (suc n)
    l4 [] any = any
    l4 (x ∷ ls) (s<sn , any) = l5 s<sn , l4 ls any where
      l5 : x < n → suc<? x r < suc n
      l5 e with x <? r
      ... | yes p = <-weaken {x} {n} e
      ... | no ¬p = e
  ws-suc2 n r (q ∪ q₁) r≤n (ws-∪ ws ws₁) = ws-∪ (ws-suc2 n r q r≤n ws) (ws-suc2 n r q₁ r≤n ws₁)
  ws-suc2 n r (q · q₁) r≤n (ws-· ws ws₁) = ws-· (ws-suc2 n r q r≤n ws) (ws-suc2 n r q₁ r≤n ws₁)
  ws-suc2 n r (ν q) r≤n (ws-ν ws) = ws-ν (ws-suc2 (suc n) (suc r) q r≤n ws)






--   g : ∀ s q n → q R s → WellScopedₛₛ s n → WellScopedₛₛ q n
--   g .(_ ∪ _) .(_ ∪ _) n (⟨⟩-∪ r r₁) (ws-∪ ws ws₁) = ws-∪ (g _ _ _ r ws) (g _ _ _ r₁ ws₁)
--   g .(_ · _) .(_ · _) n (⟨⟩-· r r₁) (ws-· ws ws₁) = ws-· (g _ _ _ r ws) (g _ _ _ r₁ ws₁)
--   g .(ν _) .(ν _) n (⟨⟩-ν r) (ws-ν ws) = ws-ν (g _ _ _ r ws)
--   g .(ν (ν qs)) .(ν (ν swapₛₛ 0 1 qs)) n (ν-swap` qs) (ws-ν (ws-ν ws)) = ws-ν (ws-ν (ws-swap2 qs 0 1 _ _ _ ws))
--   g q .(ν sucₛₛ q 0) n (ν-elim` .q) ws = ws-ν (ws-suc2 n 0 q tt ws)
--   g .(ν zs ∪ qs) .(ν (zs ∪ sucₛₛ qs 0)) n (State.ν-∪` qs zs) (State.ws-∪ (State.ws-ν ws) ws₁) = ws-ν (ws-∪ ws (ws-suc2 n 0 qs tt ws₁))
--   g .(ν zs · qs) .(ν (zs · sucₛₛ qs 0)) n (State.ν-·` qs zs) (State.ws-· (State.ws-ν ws) ws₁) = ws-ν (ws-· ws (ws-suc2 n 0 qs tt ws₁))
--   g .((x ∪ y) ∪ z) .(x ∪ y ∪ z) n (State.assoc x y z) (State.ws-∪ (State.ws-∪ ws₁ ws₂) ws) = ws-∪ ws₁ (ws-∪ ws₂ ws)
--   g q .(q ∪ 0b) n (State.rid .q) ws = ws-∪ ws ws-0b
--   g .(y ∪ x) .(x ∪ y) n (State.comm x y) (State.ws-∪ ws ws₁) = ws-∪ ws₁ ws
--   g q .(q ∪ q) n (State.idem .q) ws = ws-∪ ws ws
--   g .((x · y) · z) .(x · y · z) n (State.assoc· x y z) (State.ws-· (State.ws-· ws ws₂) ws₁) = State.ws-· ws (State.ws-· ws₂ ws₁)
--   g q .(q · 1b) n (State.rid· .q) ws = State.ws-· ws ws-1b
--   g .(y · x) .(x · y) n (State.comm· x y) (State.ws-· ws ws₁) = ws-· ws₁ ws
--   g .0b .(x · 0b) n (def∅· x) ws = {!!}
--   g .(x · y ∪ x · z) .(x · (y ∪ z)) n (State.dist x y z) ws = {!!}
--   g s .s n (refl` .s) ws = ws
--   g s q n (sym` .s .q r) ws = {!!}
--   g s q n (trans` .q y .s r r₁) ws = {!!}
--   g s q n (squash₁ .q .s r r₁ i) ws = {!!}


--   f : ∀ s q n → s R q → WellScopedₛₛ s n → WellScopedₛₛ q n
--   f .(_ ∪ _) .(_ ∪ _) n (⟨⟩-∪ r r₁) (ws-∪ ws ws₁) = ws-∪ (f _ _ _ r ws) (f _ _ _ r₁ ws₁)
--   f .(_ · _) .(_ · _) n (⟨⟩-· r r₁) (ws-· ws ws₁) = ws-· (f _ _ _ r ws) (f _ _ _ r₁ ws₁)
--   f .(ν _) .(ν _) n (⟨⟩-ν r) (ws-ν ws) = ws-ν (f _ _ _ r ws)
--   f .(ν (ν swapₛₛ 0 1 qs)) .(ν (ν qs)) n (ν-swap` qs) (ws-ν (ws-ν ws)) = ws-ν (ws-ν (ws-swap qs 0 1 _ _ _ ws))
--   f .(ν sucₛₛ q 0) q n (ν-elim` .q) (ws-ν ws) = ws-suc n 0 q tt ws
--   f .(ν (zs ∪ sucₛₛ qs 0)) .(ν zs ∪ qs) n (State.ν-∪` qs zs) (State.ws-ν (State.ws-∪ ws ws₁)) = ws-∪ (ws-ν ws) (ws-suc n 0 qs tt ws₁)
--   f .(ν (zs · sucₛₛ qs 0)) .(ν zs · qs) n (State.ν-·` qs zs) (State.ws-ν (State.ws-· ws ws₁)) = ws-· (ws-ν ws) (ws-suc n 0 qs tt ws₁)
--   f .(x ∪ y ∪ z) .((x ∪ y) ∪ z) n (State.assoc x y z) (State.ws-∪ ws (State.ws-∪ ws₁ ws₂)) = ws-∪ (ws-∪ ws ws₁) ws₂
--   f .(q ∪ 0b) q n (State.rid .q) (State.ws-∪ ws ws₁) = ws
--   f .(x ∪ y) .(y ∪ x) n (State.comm x y) (State.ws-∪ ws ws₁) = ws-∪ ws₁ ws
--   f .(q ∪ q) q n (State.idem .q) (State.ws-∪ ws ws₁) = ws
--   f .(x · y · z) .((x · y) · z) n (State.assoc· x y z) (State.ws-· ws (State.ws-· ws₁ ws₂)) = ws-· (ws-· ws ws₁) ws₂
--   f .(q · 1b) q n (State.rid· .q) (State.ws-· ws ws₁) = ws
--   f .(x · y) .(y · x) n (State.comm· x y) (State.ws-· ws ws₁) = ws-· ws₁ ws
--   f .(x · 0b) .0b n (def∅· x) ws = ws-0b
--   f .(x · (y ∪ z)) .(x · y ∪ x · z) n (State.dist x y z) (State.ws-· ws (State.ws-∪ ws₁ ws₂)) = ws-∪ (ws-· ws ws₁) (ws-· ws ws₂)
--   f s .s n (refl` .s) ws = ws
--   f s q n (sym` .q .s r) ws = g s q n r ws
--   f s q n (trans` .s y .q r r₁) ws = f y q n r₁ (f s y n r ws)
--   f s q n (squash₁ .s .q r r₁ i) ws = WSisProp q n (f s q n r ws) (f s q n r₁ ws) i







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



module _ {ℓ1} {ℓ2} {C1 : ∀ k → Type ℓ1} {C2 : ∀ k → Type ℓ2} where

  module S1 = State C1
  module S2 = State C2

  open S2

  mapₛₛ : (∀{k} → C1 k → C2 k) → (q : S1.SState) → S2.SState
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

