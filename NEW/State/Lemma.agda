{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Vec as V
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Fin hiding (_≤?_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation

module State.Lemma where

module _ where

  _<?_ : ∀ n m → Dec (n < m)
  _<?_ n m = suc n ≤? m


  suc<? : ℕ → ℕ → ℕ
  suc<? m n = l1 (m <? n) module suc≤?-1 where
    l1 : Dec (suc m ≤ n) → ℕ
    l1 (yes p) = m
    l1 (no ¬p) = suc m
  
lsuc<? : ∀{n} → Vec ℕ n →  ℕ → Vec ℕ n
lsuc<? ls n = V.map (λ x → suc<? x n) ls

const` : ∀{ℓ} → {A : Type ℓ} → A → ℕ → A
const` = const

abstract

  suc-suc : ∀ n m → m ≤ n → ∀ x → suc<? (suc<? x m) (suc n) ≡ suc<? (suc<? x n) m
  suc-suc n m rel x = l1 (x <? m) refl (x <? n) refl where
    module A = suc≤?-1 x m
    module B = suc≤?-1 x n 
    module E = suc≤?-1 x (suc n)
    module F = suc≤?-1 (suc x) (suc n)
    module G = suc≤?-1 (suc x) m
    
    l1 : (x<?m : Dec (x < m)) (eq1 : x<?m ≡ x <? m) (x<?n : Dec (x < n)) (eq2 : x<?n ≡ x <? n) →                  let module C = suc≤?-1 (A.l1 x<?m) (suc n)
                                                                                                                      module D = suc≤?-1 (B.l1 x<?n) m in
         C.l1 (A.l1 x<?m ≤? n) ≡ D.l1 (suc (B.l1 x<?n) ≤? m)

    l1 (yes x<m) eq1 (yes x<n) eq2 = J (λ x<?m _ → E.l1 (x ≤? n) ≡ A.l1 x<?m) (l2 (x ≤? n)) eq1 where
      l2 : (x≤?n : Dec (x ≤ n)) 
            → E.l1 x≤?n ≡ A.l1 (yes x<m)
      l2 (yes x≤n) = refl
      l2 (no ¬x≤n) = ⊥.rec (¬x≤n (<-weaken {x} {n} x<n))

    l1 (yes x<m) eq1 (no ¬x<n) eq2 = ⊥.rec (¬x<n (≤-trans {suc x} {m} {n} x<m rel))
    l1 (no ¬x<m) eq1 (yes x<n) eq2 = J (λ (x<?m , x<?n) _ → F.l1 x<?n ≡ A.l1 x<?m) refl (≡-× eq1 eq2)
    l1 (no ¬x<m) eq1 (no ¬x<n) eq2 = J (λ x<?n _ → F.l1 x<?n ≡ G.l1 ((suc x) <? m)) (l2 (suc x <? m)) eq2 where
      l2 : (sx<?m : Dec (suc x < m)) → suc (suc x) ≡ G.l1 sx<?m
      l2 (yes sx<m) = ⊥.rec (¬x<m (<-weaken {suc x} {m} sx<m))
      l2 (no ¬_) = refl



lsuc-lsuc : ∀{k} → ∀ n m → m ≤ n → (vs : Vec ℕ k) → lsuc<? (lsuc<? vs m) (suc n) ≡ lsuc<? (lsuc<? vs n) m
lsuc-lsuc n m rel [] = refl
lsuc-lsuc n m rel (x ∷ vs) = cong₂ _∷_ (suc-suc n m rel x) (lsuc-lsuc n m rel vs)



swap : ℕ → ℕ → ℕ → ℕ
swap m k r = l1 (m =? r) module swap-1 where
  l1 : Dec (m ≡ r) → ℕ
  l1 (yes _) = k
  l1 (no _) = l2 (k =? r) module swap-2 where
    l2 : Dec (k ≡ r) → ℕ
    l2 (yes _) = m
    l2 (no _) = r



lswap : ∀{n} → ℕ → ℕ →  Vec ℕ n → Vec ℕ n
lswap m k ls = V.map (swap m k) ls

abstract

  suc-swap : ∀ t m e → m < t → e < t → ∀ k → suc<? (swap m e k) t ≡ swap m e (suc<? k t)
  suc-swap t m e m<t e<t k = l1 (k <? t) refl where
    open swap-1 m e k renaming (l1 to swA)
    open suc≤?-1 k t renaming (l1 to s<?A)
    open suc≤?-1 e t renaming (l1 to s<?B)
    open suc≤?-1 m t renaming (l1 to s<?D)

    l1 : (k<?t : Dec (k < t)) → (eq1 : k<?t ≡ k <? t) →  let swB = swap-1.l1 m e (s<?A k<?t) 
                                                             s<?B = suc≤?-1.l1 (swA (m =? k)) t in 
       s<?B (swA (m =? k) <? t)
     ≡
       swB (m =? s<?A k<?t)
    l1 (yes k<t) eq1 = l2 (m =? k) where
      l2 : (m=?k : Dec (m ≡ k)) →              let s<?B = suc≤?-1.l1 (swA m=?k) t in
      
            s<?B (swA m=?k <? t) ≡ swA m=?k
      l2 (yes _) = l3 (e <? t) where
        l3 : (e<?t : Dec (suc e ≤ t)) → s<?B e<?t ≡ e
        l3 (yes _) = refl
        l3 (no ¬e<t) = ⊥.rec (¬e<t e<t)

      l2 (no ¬p) = l3 (e =? k) where
        open swap-2 ¬p renaming (l2 to swC)
        l3 : (e=?k : Dec (e ≡ k)) →                              let s<?C = suc≤?-1.l1 (swC e=?k) t in
             s<?C ((swC e=?k) <? t) ≡ swC e=?k
        l3 (yes _) = l4 (m <? t) where
          l4 : (m<?t : Dec (m < t)) → s<?D m<?t ≡ m
          l4 (yes _) = refl
          l4 (no ¬m<t) = ⊥.rec (¬m<t m<t)
          
        l3 (no ¬p) = J (λ k<?t x → s<?A k<?t ≡ k) refl eq1

    l1 (no ¬k<t) eq1 = l2 (m =? k) (m =? suc k) where
      open swap-1 m e (suc k) renaming (l1 to swB)
      l2 : (m=?k : Dec (m ≡ k)) → (m=?sk : Dec (m ≡ suc k)) →       let s<?C = suc≤?-1.l1 (swA m=?k) t in
             s<?C ((swA m=?k) <? t)
           ≡
             swB m=?sk
      l2 (yes m≡k) _ = ⊥.rec (¬k<t (J (λ y x → y < t) m<t m≡k))
      l2 (no _) (yes m≡sk) = ⊥.rec (¬k<t ( <-weaken {suc k} {t} (J (λ y x → y < t) m<t m≡sk)))
      l2 (no ¬p1) (no ¬p2) = l3 (e =? k) (e =? suc k) where
        open swap-1.swap-2 m e k ¬p1 renaming (l2 to swE)
        open swap-1.swap-2 m e (suc k) ¬p2 renaming (l2 to swF)
        l3 : (e=?k : Dec (e ≡ k)) (e=?sk : Dec (e ≡ suc k)) →       let s<?C = suc≤?-1.l1 (swE e=?k) t in 
             s<?C (suc (swE e=?k) ≤? t) ≡ swF e=?sk
        l3 (yes e≡k) _ = ⊥.rec (¬k<t (J (λ y x → y < t) e<t e≡k))
        l3 (no _) (yes e≡sk) = ⊥.rec (¬k<t ( <-weaken {suc k} {t} (J (λ y x → y < t) e<t e≡sk)))
        l3 (no _) (no ¬p) = J (λ y _ → s<?A y ≡ suc k) refl eq1


lsuc-lswap : ∀{k} → ∀ t m e → m < t → e < t → (vs : Vec ℕ k) → lsuc<? (lswap m e vs) t ≡ lswap m e (lsuc<? vs t)
lsuc-lswap t m e rel1 rel2 [] = refl
lsuc-lswap t m e rel1 rel2 (x ∷ vs) = cong₂ _∷_ (suc-swap t m e rel1 rel2 x) (lsuc-lswap t m e rel1 rel2 vs)

postulate
  suc-swap> : ∀ t m e → t ≤ m → t ≤ e → ∀ k → suc<? (swap m e k) t ≡ swap (suc m) (suc e) (suc<? k t)

lsuc-lswap> : ∀{k} → ∀ t m e → t ≤ m → t ≤ e → (vs : Vec ℕ k) → lsuc<? (lswap m e vs) t ≡ lswap (suc m) (suc e) (lsuc<? vs t)
lsuc-lswap> t m e t≤m t≤e [] = refl
lsuc-lswap> t m e t≤m t≤e (x ∷ vs) = cong₂ _∷_ (suc-swap> t m e t≤m t≤e x) (lsuc-lswap> t m e t≤m t≤e vs)


abstract
  swap-swap : ∀ t1 t2 e1 e2 → ¬ (t1 ≡ e1) → ¬ (t1 ≡ e2) →  ¬ (t2 ≡ e1) → ¬ (t2 ≡ e2) → ∀ k → swap t1 t2 (swap e1 e2 k) ≡ swap e1 e2 (swap t1 t2 k)
  swap-swap t1 t2 e1 e2 t1≢e1 t1≢e2 t2≢e1 t2≢e2 k = l1 (t1 =? k) (e1 =? k)  where
    open swap-1 e1 e2 k renaming (l1 to fst=?E)
    open swap-1 t1 t2 k renaming (l1 to fst=?T)
    l1 : (t1=?k : Dec (t1 ≡ k)) (e1=?k : Dec (e1 ≡ k)) →
                                                             let fst=?T2 = swap-1.l1 t1 t2 (fst=?E e1=?k)
                                                                 fst=?E2 = swap-1.l1 e1 e2 (fst=?T t1=?k) in
     
       fst=?T2 (t1 =? fst=?E e1=?k)
       ≡
       fst=?E2 (e1 =? fst=?T t1=?k)
    l1 (yes t1≡k) (yes e1≡k) = ⊥.rec (t1≢e1 (t1≡k ∙ sym e1≡k))
    l1 (yes t1≡k) (no ¬p2) = l2 (e2 =? k) (e1 =? t2) where
      l2 : (e2=?k : Dec (e2 ≡ k)) (e1=?t2 : Dec (e1 ≡ t2)) →    let snd=?E = swap-1.swap-2.l2 e1 e2 k ¬p2
                                                                    fst=?T3 = swap-1.l1 t1 t2 (snd=?E e2=?k)
                                                                    fst=?E3 = swap-1.l1 e1 e2 t2
                                                                    in
        fst=?T3 (t1 =? snd=?E e2=?k)
         ≡ fst=?E3 e1=?t2
      l2 e2=?k (yes e1≡t2) = ⊥.rec (t2≢e1 (sym e1≡t2))
      l2 (yes p) (no _) = ⊥.rec (t1≢e2 (t1≡k ∙ sym p))
      l2 (no ¬p) (no ¬p2) = l3 (t1 =? k) (e2 =? t2) where
        l3 : (t1=?k : Dec (t1 ≡ k)) (e2=?t2 : Dec (e2 ≡ t2)) →     let snd=?E4 = swap-1.swap-2.l2 e1 e2 t2 ¬p2
                                                                   in
             fst=?T t1=?k ≡ snd=?E4 e2=?t2
        l3 (yes p) (yes e2≡t2) = ⊥.rec (t2≢e2 (sym e2≡t2))
        l3 (yes p) (no ¬p) = refl
        l3 (no t1≢k) e2=?t2 = ⊥.rec (t1≢k t1≡k)


    l1 (no ¬p1) (yes e1≡k) with t1 =? e2 | t2 =? k
    ... | yes t1≡e2 | q = ⊥.rec (t1≢e2 t1≡e2)
    ... | no ¬p | yes t2≡k = ⊥.rec (t2≢e1 (t2≡k ∙ sym e1≡k))
    ... | no ¬p | no ¬p₁ with t2 =? e2 | e1 =? k
    ... | yes t2≡e2 | yes p = ⊥.rec (t2≢e2 t2≡e2)
    ... | no ¬p₂ | yes p = refl
    ... | r | no e1≢k = ⊥.rec (e1≢k e1≡k)
    l1 (no t1≢k) (no e1≢k) with e2 =? k | t2 =? k
    ... | yes e2≡k | yes t2≡k = ⊥.rec (t2≢e2 (t2≡k ∙ sym e2≡k))
    ... | no e2≢k | yes t2≡k = l4 (t1 =? k) (e1 =? t1) where
      l4 : (w : Dec (t1 ≡ k)) (w₁ : Dec (e1 ≡ t1)) →
           fst=?T w ≡ swap-1.l1 e1 e2 t1 w₁
      l4 w (yes e1≡t1) = ⊥.rec (t1≢e1 (sym e1≡t1))
      l4 (yes t1≡k) (no ¬p) with e2 =? t1
      ... | yes e2≡t1 = ⊥.rec (t1≢e2 (sym e2≡t1))
      ... | no ¬p₁ = t2≡k ∙ (sym t1≡k)
      l4 (no ¬p₁) (no ¬p) with e2 =? t1
      ... | yes e2≡t1 = ⊥.rec (t1≢e2 (sym e2≡t1))
      ... | no ¬p₂ with t2 =? k
      ... | yes p = refl
      ... | no t2≢k = ⊥.rec (t2≢k t2≡k)
    ... | no e2≢k | no t2≢k = l3 (t1 =? k) (e1 =? k) where
      l3 : (w : Dec (t1 ≡ k)) (w₁ : Dec (e1 ≡ k)) → fst=?T w ≡ fst=?E w₁
      l3 (yes t1≡k) (yes e1≡k) = ⊥.rec (t1≢e1 (t1≡k ∙ sym e1≡k))
      l3 (yes t1≡k)= ⊥.rec (t1≢k t1≡k)
      l3 (no ¬p) (yes e1≡k) = ⊥.rec (e1≢k e1≡k)
      l3 (no t1≢k) (no ¬p₁) with t2 =? k | e2 =? k
      ... | yes t2≡k | r = ⊥.rec (t2≢k t2≡k)
      ... | no ¬p₂ | yes e2≡k = ⊥.rec (e2≢k e2≡k)
      ... | no ¬p₂ | no ¬p₃ = refl
    ... | yes e2≡k | no ¬p with (t1 =? e1) | (e1 =? k)
    ... | yes t1≡e1 | q = ⊥.rec (t1≢e1 t1≡e1)
    ... | no ¬p₁ | yes e1≡k = l2 (t2 =? e1) where
      l2 : (w : Dec (t2 ≡ e1)) → swap-1.swap-2.l2 t1 t2 e1 ¬p₁ w ≡ e2
      l2 (yes t2≡e1) = ⊥.rec (t2≢e1 t2≡e1)
      l2 (no ¬p) = e1≡k ∙ sym e2≡k
    ... | no ¬p₁ | no ¬p₂ with (t2 =? e1) | (e2 =? k)
    ... | yes t2≡e1 | r = ⊥.rec (t2≢e1 t2≡e1)
    ... | no ¬p₃ | yes p = refl
    ... | no ¬p₃ | no e2≢k = ⊥.rec (e2≢k e2≡k)



lswap-lswap : ∀{k} → ∀ t1 t2 e1 e2 → ¬ (t1 ≡ e1) → ¬ (t1 ≡ e2) →  ¬ (t2 ≡ e1) → ¬ (t2 ≡ e2) → (vs : Vec ℕ k)
              → lswap t1 t2 (lswap e1 e2 vs) ≡ lswap e1 e2 (lswap t1 t2 vs)
lswap-lswap t1 t2 e1 e2 x x₁ x₂ x₃ [] = refl
lswap-lswap t1 t2 e1 e2 x x₁ x₂ x₃ (x₄ ∷ vs) = cong₂ _∷_ (swap-swap t1 t2 e1 e2 x x₁ x₂ x₃ x₄) (lswap-lswap t1 t2 e1 e2 x x₁ x₂ x₃ vs)

