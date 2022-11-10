{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as M
open import Cubical.Data.List
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import SemiRing

module State where


data _∈_ (n : ℕ) : List ℕ → Set where
  here : ∀{ns} → n ∈ (n ∷ ns) 
  there : ∀{k ns} → n ∈ ns → n ∈ (k ∷ ns) 

data _⊃_ (ns : List ℕ) : List ℕ → Set where
  nomore : ns ⊃ []
  more : ∀{k ks} → k ∈ ns → ns ⊃ ks → ns ⊃ (k ∷ ks) 

?Secrets : Type
?Secrets = Maybe (List ℕ)

pattern ∅ = nothing
pattern ! x = just x

data RR : ?Secrets → ?Secrets → ?Secrets → Set where
  rr : ∀{l1 l2 l} → l ⊃ l1 → l ⊃ l2 → RR (! l1) (! l2) (! l)
  r∅ : ∀{l1 l} → l ⊃ l1 → RR (! l1) ∅ (! l)
  ∅r : ∀{l2 l} → l ⊃ l2 → RR ∅ (! l2) (! l)
  ∅∅ : RR ∅ ∅ ∅

data QQ : ?Secrets → ?Secrets → ?Secrets → Set where
  rr : ∀{l1 l2 l} → l ⊃ l1 → l ⊃ l2 → QQ (! l1) (! l2) (! l)
  r∅ : ∀{l1} → QQ (! l1) ∅ ∅
  ∅r : ∀{l2} → QQ ∅ (! l2) ∅
  ∅∅ : QQ ∅ ∅ ∅

asuc : List ℕ → List ℕ
asuc [] = []
asuc (x ∷ xs) = suc x ∷ asuc xs

apred : List ℕ → List ℕ
apred [] = []
apred (zero ∷ xs) = xs
apred (suc x ∷ xs) = x ∷ apred xs

qpred : ℕ → List ℕ → List ℕ
qpred n [] = []
qpred n (l ∷ ls)
  = case (n ≟ l) of
      λ { (lt _) → predℕ l ∷ qpred n ls ;
          _ → l ∷ qpred n ls}


data ListSuc : List ℕ → Set where
  nomore : ListSuc []
  more : ∀{n ns} → ListSuc ns → ListSuc (suc n ∷ ns)




_>>=_ : ∀{ℓ1 ℓ2 D A} → Maybe {ℓ1} D → (D → Maybe A) → Maybe {ℓ2} A
nothing >>= f = nothing
just x >>= f = f x

_+|_|+ₘ_ : ∀{ℓ1 D} → Maybe {ℓ1} D → (D → D → D) → Maybe {ℓ1} D → Maybe D
nothing +| f |+ₘ y = y
just x +| f |+ₘ nothing = just x
just x +| f |+ₘ just y = just (f x y)


lsuc : List ℕ → List ℕ
lsuc [] = []
lsuc (x ∷ xs) = suc x ∷ xs

lpred : List ℕ → List ℕ
lpred [] = []
lpred (zero ∷ xs) = xs
lpred (suc x ∷ xs) = x ∷ xs

g : List ℕ → List ℕ → List ℕ
g [] ys = ys
g xs [] = xs
g (zero ∷ xs) (zero ∷ ys) = zero ∷ g xs ys
g (zero ∷ xs) (suc y ∷ ys) = zero ∷ g xs (y ∷ ys)
g (suc x ∷ xs) (zero ∷ ys) = zero ∷ g (x ∷ xs) ys
g (suc x ∷ xs) (suc y ∷ ys) = lsuc (g (x ∷ xs) (y ∷ ys))



private
  variable
    ℓ : Level

infixr 5 _∪_
infixr 7 _·_
infixr 10 `_

module _ (C : (List ℕ) → Type ℓ) where

  mutual
  
    data State : Type ℓ where  
      0b      : State
      1b      : State
      `_      : ∀{l} → (∀ l → C l) → State
      _∪_     : State → State → State 
      _·_     : State → State → State
      ν_      : State → State
      ν-elim  : ∀{q} → 0 ∉ₛ q → ν q ≡ apredq 0 q
      squash  : isSet (State)
      assoc   : {x y z : State} → (x ∪ (y ∪ z)) ≡ ((x ∪ y) ∪ z)
      rid     : {x : State} → x ∪ 0b ≡ x
      comm    : {x y : State} → x ∪ y ≡ y ∪ x
-- Equal terms here mean that we have equal state, but maybe we can have different actors (locationwise),
-- This also means that actors that the secret of ν does not play a role in the equality here.
-- In other words, as long as the structure is the same, it is the same state.
      idem    : {x : State} → x ∪ x ≡ x
      assoc·   : {x y z : State} → x · (y · z) ≡ (x · y) · z
      rid·     : {x : State} → x · 1b ≡ x
      comm·    : {x y : State} → x · y ≡ y · x
      def∅·   : {x : State} → x · 0b ≡ 0b
      dist    : {x y z : State} → x · (y ∪ z) ≡ (x · y) ∪ (x · z)


    data E : State → ?Secrets → Type ℓ where
      e0b : E 0b ∅
      e1b : E 1b (! [])
      e` : ∀ {l a} → E (`_ {l} a) (! l)
      e∪ : ∀{l1 l2 l} → ∀ q1 q2 → E q1 l1 → E q2 l2 → RR l1 l2 l → E (q1 ∪ q2) l
      e· : ∀{l1 l2 l} → ∀ q1 q2 → E q1 l1 → E q2 l2 → QQ l1 l2 l → E (q1 · q2) l
      eν : ∀{l1 l} → ∀ q → E q l1 → l ≡ (l1 >>= λ l → (! (apred l))) → E (ν q) l 

    
    data EE (q : State) : Type ℓ where
      ee∅ : E q ∅ → EE q
      ee[] : E q (! []) → EE q
     ---  ??
      ee! : ∀{l} → ListSuc l → E q (! l) → EE q


   


      


    data Is0b : State → Type ℓ where
      0bc : Is0b 0b
      ·lc  : ∀{x c} → Is0b x → Is0b (x · c)
      ·rc  : ∀{x c} → Is0b c → Is0b (x · c)
      ∪c   : ∀{x c} → Is0b x → Is0b c → Is0b (x ∪ c)


  
    data _∉ₛ_ : ℕ → State → Type ℓ where
      0bc   : ∀{n s} → Is0b s → n ∉ₛ s
      1bc   : ∀{n} → n ∉ₛ 1b
      `c    : ∀{n} → ∀{l C} → ¬ (n ∈ l) → n ∉ₛ (`_ {l} C)
      _∪c_  : ∀{n s1 s2} → n ∉ₛ s1 → n ∉ₛ s2 → n ∉ₛ (s1 ∪ s2)
      _·c_  : ∀{n s1 s2} → (n ∉ₛ s1) → (n ∉ₛ s2) → n ∉ₛ (s1 · s2)
      _·lc_ : ∀{n s1 s2} → Is0b s1 → n ∉ₛ (s1 · s2)
      _·rc_ : ∀{n s1 s2} → Is0b s2 → n ∉ₛ (s1 · s2)
      νc_    : ∀{n s} → (suc n ∉ₛ s) → n ∉ₛ (ν s)

    apredq : ℕ → (q : State) → State
    apredq n 0b = 0b
    apredq n 1b = 1b
    apredq n (`_ {l} x) = `_ {qpred n l} x
    apredq n (q1 ∪ q2) = apredq n q1 ∪ apredq n q2
    apredq n (q1 · q2) = apredq n q1 · apredq n q2
    apredq n (ν q) = ν (apredq (suc n) q)
    apredq n (ν-elim x i) = {!!}  -- apredq 0 (apredq (suc n) q) = apredq n (apredq 0 q)
    apredq n (squash q q₁ x y i i₁) = {!!}
    apredq n (assoc i) = {!!}
    apredq n (rid i) = {!!}
    apredq n (comm i) = {!!}
    apredq n (idem i) = {!!}
    apredq n (assoc· i) = {!!}
    apredq n (rid· i) = {!!}
    apredq n (comm· i) = {!!}
    apredq n (def∅· i) = {!!}
    apredq n (dist i) = {!!}

    e1 : ∀ n q → 0 ∉ₛ q → 0 ∉ₛ apredq (suc n) q
    e1 n q (0bc x) = {!!}
    e1 n .1b 1bc = 1bc
    e1 n .(` _) (`c x) = {!`c ?!}
    e1 n .(_ ∪ _) (x ∪c x₁) = {!!}
    e1 n .(_ · _) (x ·c x₁) = {!!}
    e1 n .(_ · _) (_·lc_ x) = {!!}
    e1 n .(_ · _) (_·rc_ x) = {!!}
    e1 n .(ν _) (νc x) = {!!}

  ff : ∀ s → Is0b s → s ≡ 0b
  ff .0b 0bc = refl
  ff .(_ · _) (·lc {x} {c} e) = cong (λ x → x · c) (ff x e) ∙ comm· ∙ def∅·
  ff .(_ · _) (·rc {x} {c} e) = cong (λ c → x · c) (ff c e) ∙ def∅·
  ff .(_ ∪ _) (∪c e1 e2) = cong₂ _∪_ (ff _ e1) (ff _ e2) ∙ rid




    -- -- DD : State → Type
    -- -- DD q = (ee q ≡ []) ⊎ (∃[ n ∈ ℕ ] ∃[ xs ∈ List ℕ ] (ee q) ≡ suc n ∷ xs)

    -- -- DDD : State → Type ℓ
    -- -- DDD q = E q nothing ⊎ (E q (just []) ⊎ Σ ℕ λ n → Σ (List ℕ) λ xs → E q (just (suc n ∷ xs)))

    -- -- data E : State → Maybe (List ℕ) → Type ℓ where
    -- --   e0b : E 0b nothing
    -- --   e1b : E 1b (just [])
    -- --   e` : ∀ {l x} → E (`_ {l} x) (just l)
    -- --   e∪ : ∀{l1 l2} → ∀ q1 q2 → E q1 l1 → E q2 l2 → E (q1 ∪ q2) (l1 +| g |+ₘ l2)
    -- --   e· : ∀{l1 l2} → ∀ q1 q2 → E q1 l1 → E q2 l2 → E (q1 · q2) (l1 >>= λ l1 → l2 >>= λ l2 → just (g l1 l2))
    -- --   eν : ∀{l} → ∀ q → E q l → E (ν q) (l >>= λ l → just (lpred l))

    -- -- e : (q : State) → Σ (Maybe (List ℕ)) (λ m → (E q m))
    -- -- e 0b = nothing , e0b
    -- -- e 1b = just [] , e1b
    -- -- e (`_ {l} x) = just l , e`
    -- -- e (q1 ∪ q2) = fst (e q1) +| g |+ₘ fst (e q2) , e∪ q1 q2 (snd (e q1)) (snd (e q2))
    -- -- e (q1 · q2) = ((fst (e q1)) >>= λ l1 → (fst (e q2)) >>= λ l2 → just (g l1 l2)) , e· q1 q2 (snd (e q1)) (snd (e q2))
    -- -- e (ν q) = (fst (e q) >>= λ l → just (lpred l)) , eν q (snd (e q))
    -- -- e (squash a b p1 p2 i j) = {!!} -- isOfHLevel→isOfHLevelDep 2 (λ _ → isOfHLevelMaybe 0 (isOfHLevelList 0 isSetℕ)) (e a) (e b) (cong e p1) (cong e p2) (squash a b p1 p2) i j
    -- -- e (assoc i) = {!!}
    -- -- e (rid i) = {!!}
    -- -- e (comm i) = {!!}
    -- -- e (idem i) = {!!}
    -- -- e (assoc· i) = {!!}
    -- -- e (rid· i) = {!!}
    -- -- e (comm· i) = {!!}
    -- -- e (def∅· i) = {!!}
    -- -- e (dist i) = {!!}
  
    -- -- ee : State → List ℕ
    -- -- ee q = M.rec [] (λ x → x) {!!} -- (e q)
  
    -- -- lpredq : (q : State) → DDD q → State
    -- -- lpredq 0b e = 0b
    -- -- lpredq 1b e = 1b
    -- -- lpredq (` x) (inl e) = {!!}
    -- -- lpredq (` x) (inr e) = {!!}
    -- -- lpredq (q ∪ q₁) e = {!!}
    -- -- lpredq (q · q₁) e = {!!}
    -- -- lpredq (ν q) e = {!!}
    -- -- lpredq (ν-elim x i) e = {!!}
    -- -- lpredq (squash q q₁ x y i i₁) e = {!!}
    -- -- lpredq (assoc i) e = {!!}
    -- -- lpredq (rid i) e = {!!}
    -- -- lpredq (comm i) e = {!!}
    -- -- lpredq (idem i) e = {!!}
    -- -- lpredq (assoc· i) e = {!!}
    -- -- lpredq (rid· i) e = {!!}
    -- -- lpredq (comm· i) e = {!!}
    -- -- lpredq (def∅· i) e = {!!}
    -- -- lpredq (dist i) e = {!!}
