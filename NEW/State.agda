{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as M
open import Cubical.Data.List
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import SemiRing

module State where


-- data _∈_ (n : ℕ) : List ℕ → Set where
--   here : ∀{ns} → n ∈ (n ∷ ns) 
--   there : ∀{k ns} → n ∈ ns → n ∈ (k ∷ ns) 
-- 
-- data _⊃_ (ns : List ℕ) : List ℕ → Set where
--   nomore : ns ⊃ []
--   more : ∀{k ks} → k ∈ ns → ns ⊃ ks → ns ⊃ (k ∷ ks) 

lookup : ℕ → List ℕ → Bool
lookup n [] = false
lookup n (l ∷ ls) = =?rec (n =? l) module _ where
  =?rec : Dec (n ≡ l) → Bool
  =?rec (yes _) = true
  =?rec _ = lookup n ls

_∈_ : ∀ n ls → Type
n ∈ ls = Bool→Type (lookup n ls)

_∉_ : ∀ n ls → Type
n ∉ ls = ¬ n ∈ ls

lem2 : ∀ n l1 l2 → lookup n (l1 ++ l2) ≡ lookup n l1 or lookup n l2
lem2 n [] l2 = refl
lem2 n (x ∷ l1) l2 with n =? x
... | yes _ = refl
... | no _ =  lem2 n l1 l2


pred? : ∀ n l → Dec (n ≤ l) → ℕ
pred? _ l (yes _) = predℕ l 
pred? _ l (no _) = l

pred?-pred? : ∀ n m l → ((¬ n ≡ l) ⊎ (m ≤ l)) × ((¬ m ≡ l) ⊎ (n ≤ l)) → (dn : Dec (suc n ≤ l)) → (dm : Dec (suc m ≤ l))
      → (dml : Dec (m ≤ pred? (suc n) l dn)) → (dnl : Dec (n ≤ pred? (suc m) l dm))
      → pred? m _ dml ≡ pred? n _ dnl
pred?-pred? n m (suc l) q (yes p) (yes p₁) (yes p₂) (yes p₃) = refl
pred?-pred? n m (suc l) q (yes p) (yes p₁) (yes p₂) (no ¬p) = ⊥.rec (¬p p)
pred?-pred? n m (suc l) q (yes p) (yes p₁) (no ¬p) dnl = ⊥.rec (¬p p₁)
pred?-pred? n m (suc l) q (yes p) (no ¬p) (yes p₂) (yes p₁) = ⊥.rec (¬p p₂)
pred?-pred? n m (suc l) q (yes p) (no ¬p) (no ¬p₁) (yes p₁) = refl
pred?-pred? n m (suc l) q (yes p) (no ¬p) dml (no ¬p₁) = ⊥.rec (¬p₁ (≤-trans {k = n} {m = l} p (n≤k+n l)))
pred?-pred? n m (suc l) q (no ¬p) (yes p) dml (yes p₁) = ⊥.rec (¬p p₁)
pred?-pred? n m (suc l) q (no ¬p) (yes p) (yes p₁) (no ¬p₁) = refl
pred?-pred? n m (suc l) q (no ¬p) (yes p) (no ¬p₂) (no ¬p₁) = ⊥.rec (⊥.rec (¬p₂ (≤-trans {k = m} {m = l} p (n≤k+n l))))
pred?-pred? n m l q (no ¬p) (no ¬p₁) (yes p) (yes p₁) = refl
pred?-pred? n m l (f , inl x) (no ¬p) (no ¬p₁) (yes p) (no ¬p₂) = ⊥.rec (x (≤-¬<-≡ p ¬p₁))
pred?-pred? n m l (f , inr x) (no ¬p) (no ¬p₁) (yes p) (no ¬p₂) = ⊥.rec (¬p₂ x)
pred?-pred? n m l (inl x , s) (no ¬p) (no ¬p₁) (no ¬p₂) (yes p) = ⊥.rec (x (≤-¬<-≡ p ¬p))
pred?-pred? n m l (inr x , s) (no ¬p) (no ¬p₁) (no ¬p₂) (yes p) = ⊥.rec (¬p₂ x)
pred?-pred? n m l q (no ¬p) (no ¬p₁) (no ¬p₂) (no ¬p₃) = refl

lpred[*>_] : ℕ → List ℕ → List ℕ
lpred[*>_] n [] = []
lpred[*>_] n (l ∷ ls) = pred? (suc n) l (suc n ≤? l) ∷ lpred[*>_] n ls

lpred++ : ∀ n l1 l2 → lpred[*> n ] (l1 ++ l2) ≡ (lpred[*> n ] l1) ++ (lpred[*> n ] l2)
lpred++ n [] l2 = refl
lpred++ n (l ∷ l1) l2 = cong (_ ∷_) (lpred++ n l1 l2)

∈-pred<l : ∀ m n q → m ≤ n → m ∈ q → m ∈ lpred[*> n ] q
∈-pred<l m n [] rel eqq = eqq
∈-pred<l m n (x ∷ ls) rel eqq with (suc n ≤? x)
... | no ¬p with m ≟ x
∈-pred<l m n (x ∷ ls) rel eqq | no ¬p | eq x₁ = tt
∈-pred<l m n (x ∷ ls) rel eqq | no ¬p | lt x₁ = ∈-pred<l m n ls rel eqq
∈-pred<l m n (x ∷ ls) rel eqq | no ¬p | gt x₁ = ∈-pred<l m n ls rel eqq
∈-pred<l m n (x ∷ ls) rel eqq | yes p with m ≟ predℕ x | m ≟ x
... | eq x₁ | r = tt
... | lt x₁ | lt x₂ = ∈-pred<l m n ls rel eqq
∈-pred<l m n (suc x ∷ ls) rel eqq | yes p | lt x₁ | eq x₂ = ⊥.rec (¬m<m {m = x} (<-weaken {m = suc x} {n = x} (subst (λ z → z < x) x₂ x₁)))
... | lt x₁ | gt x₂ = ∈-pred<l m n ls rel eqq
∈-pred<l m n (suc x ∷ ls) rel eqq | yes p | gt x₁ | r = ⊥.rec (¬m<m {m = m} (≤-trans {suc m} {suc n} {m} rel (≤-trans {suc n} {suc x} {m} p x₁)))

∈-pred<r : ∀ m n q → m < n → m ∈ lpred[*> n ] q → m ∈ q
∈-pred<r m n [] rel eqq = eqq
∈-pred<r m n (x ∷ ls) rel eqq  with (suc n ≤? x)
... | no ¬p with m ≟ x
∈-pred<r m n (x ∷ ls) rel eqq | no ¬p | eq x₁ = tt
∈-pred<r m n (x ∷ ls) rel eqq | no ¬p | lt x₁ = ∈-pred<r m n ls rel eqq
∈-pred<r m n (x ∷ ls) rel eqq | no ¬p | gt x₁ = ∈-pred<r m n ls rel eqq
∈-pred<r m n (x ∷ ls) rel eqq | yes p with m ≟ predℕ x | m ≟ x
... | r | eq x₁ = tt 
∈-pred<r m n (suc x ∷ ls) rel eqq | yes p | eq x₂ | lt x₁ = ⊥.rec (¬m<m {m = m} (≤-trans {suc m} {n} {m} rel (subst (λ z → n ≤ z) (sym x₂) p)))
... | lt x₂ | lt x₁ = ∈-pred<r m n ls rel eqq
... | gt x₂ | lt x₁ = ∈-pred<r m n ls rel eqq
... | r | gt x₁ = ⊥.rec (¬m<m {m = 3 + m} (≤-trans {3 + m} {2 + n} {2 + m} rel (<-weaken {n} {m} (<-trans {n} {x} {m} p x₁))))



lpred-lpred : ∀ n m l → suc n ∉ l → suc m ∉ l → lpred[*> m ] (lpred[*> suc n ] l) ≡ lpred[*> n ] (lpred[*> suc m ] l)
lpred-lpred n m [] inn inm = refl
lpred-lpred n m (l ∷ []) inn inm with suc m =? l | suc n =? l
... | no ¬w | no ¬p
 = cong (_∷ []) (pred?-pred? (suc n) (suc m) l (inl ¬p , inl ¬w) (suc (suc n) ≤? l) (suc (suc m) ≤? l) (suc m ≤? pred? (suc (suc n)) l (suc (suc n) ≤? l)) (suc n ≤? pred? (suc (suc m)) l (suc (suc m) ≤? l)))
... | no ¬w | yes p = ⊥.rec (inn tt)
... | yes p | q = ⊥.rec (inm tt)
lpred-lpred n m (l ∷ ls) inn inm with (suc m =? l) | (suc n =? l)
... | yes p | q = ⊥.rec (inm tt)
... | no ¬p | yes p = ⊥.rec (inn tt)
... | no ¬p | no ¬p₁ = cong lpred[*> m ] (lpred++ (suc n) [ l ] ls) ∙ lpred++ m (lpred[*> suc n ] [ l ]) (lpred[*> suc n ] ls) ∙ cong₂ _++_ (lpred-lpred n m [ l ] (l1 (suc n =? l)) (l2 (suc m =? l))) (lpred-lpred n m ls inn inm) where
  l1 : ∀ dn → ¬ (Bool→Type (=?rec (suc n) l [] dn))
  l1 (yes p) = ⊥.rec (¬p₁ p)
  l1 (no ¬p) = λ z → z
  l2 : ∀ dm → ¬ (Bool→Type (=?rec (suc m) l [] dm))
  l2 (yes p) = ⊥.rec (¬p p)
  l2 (no ¬p) = λ z → z

lpred-lpred-0 : ∀ n l → lpred[*> 0 ] (lpred[*> suc n ] l) ≡ lpred[*> n ] (lpred[*> 0 ] l)
lpred-lpred-0 n [] = refl
lpred-lpred-0 n (zero ∷ ls) with n ≤? zero
... | yes p = cong (zero ∷_) (lpred-lpred-0 n ls)
... | no ¬p = cong (zero ∷_) (lpred-lpred-0 n ls)
lpred-lpred-0 n (suc l ∷ ls) with suc n ≤? l
... | no ¬p = cong (l ∷_) (lpred-lpred-0 n ls)
... | yes p with 1 ≤? l
... | yes p1 = cong (predℕ l ∷_) (lpred-lpred-0 n ls)
... | no ¬p = ⊥.rec (¬p (≤-trans {1} {suc n} {l} tt p))



-- dd : ∀{l m n} → ¬ (m ∈ l) → ¬ (m ∈ lpred[*> m + suc n ] l)
-- dd {[]} {m} {n} x = x
-- dd {l ∷ ls} {m} {n} x w with ((m + suc n) ≟ l)
-- dd {l ∷ ls} {.(predℕ l)} {n} x here | lt rel = l1 rel where
--   l1 : ∀{l} → ¬ (predℕ l + suc n < l)
--   l1 {zero} x = snotz (≤-antisym x zero-≤ )
--   l1 {suc l} x = snotz (inj-m+ ((cong suc (refl ∙ (+-assoc l (suc n) (fst x))) ∙ (+-comm (suc (l + suc n)) ( fst x))) ∙ snd x ∙ sym (+-zero _)))
-- dd {l ∷ ls} {m} {n} x (there w) | lt rel = dd (λ e → x (there e)) w
-- dd {l ∷ ls} {.l} {n} x here | eq rel = x here
-- dd {l ∷ ls} {m} {n} x (there w) | eq rel = dd (λ e → x (there e)) w
-- dd {l ∷ ls} {.l} {n} x here | gt rel = x here
-- dd {l ∷ ls} {m} {n} x (there w) | gt rel = dd (λ e → x (there e)) w


-- ss : ∀{l m n} → ¬ (m ∈ l) → m < n → ¬ (m ∈ lpred[*> n ] l)
-- ss {l} {m} {n} x (fst₁ , snd₁) = J (λ y eq → ¬ (m ∈ lpred[*> y ] l)) (dd x) ((+-comm m (suc fst₁) ∙ (sym (+-suc _ _))) ∙ snd₁)

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
      ν-elim  : ∀{q} → 0 P∉ₛ q → ν q ≡ predₛ 0 q
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

    {-# TERMINATING #-}
    0b? : State → Bool
    0b? 0b = true
    0b? 1b = false
    0b? (` x) = false
    0b? (s ∪ s₁) = 0b? s and 0b? s₁
    0b? (s · s₁) = 0b? s or 0b? s₁
    0b? (ν s) = 0b? s
    0b? (ν-elim {q = q} x i) = l1 0 q i
    0b? (squash s s₁ x y i i₁) = isSetBool (0b? s) (0b? s₁) (cong 0b? x) (cong 0b? y) i i₁
    0b? (assoc {x} {y} {z} i) = and-assoc (0b? x) (0b? y) (0b? z) i
    0b? (rid {x} i) = and-identityʳ (0b? x) i
    0b? (comm {x} {y} i) = and-comm (0b? x) (0b? y) i
    0b? (idem {x} i) = and-idem (0b? x) i
    0b? (assoc· {x} {y} {z} i) = or-assoc (0b? x) (0b? y) (0b? z) i
    0b? (rid· {x} i) = or-identityʳ (0b? x) i
    0b? (comm· {x} {y} i) = or-comm (0b? x) (0b? y) i
    0b? (def∅· {x} i) = zeroʳ (0b? x) i
    0b? (dist {x} {y} {z} i) = or-and-dist (0b? x) (0b? y) (0b? z) i


    _∈ₛ_ : ℕ → State → Bool
    n ∈ₛ 0b = false
    n ∈ₛ 1b = false
    n ∈ₛ (`_ {l} x) = lookup n l
    n ∈ₛ (x ∪ x₁) = n ∈ₛ x or n ∈ₛ x₁
    n ∈ₛ (x · x₁) = (n ∈ₛ x and not (0b? x₁)) or (n ∈ₛ x₁ and not (0b? x))
    n ∈ₛ (ν x) = (suc n) ∈ₛ x
    n ∈ₛ ν-elim {q = q} 0∉q i = {!!}
    n ∈ₛ squash x x₁ p p₁ i i₁ = isSetBool (n ∈ₛ x) (n ∈ₛ x₁) (cong (n ∈ₛ_) p) (cong (n ∈ₛ_) p₁) i i₁
    n ∈ₛ assoc {x} {y} {z} i = or-assoc (n ∈ₛ x) (n ∈ₛ y) (n ∈ₛ z) i
    n ∈ₛ rid {x} i = or-identityʳ (n ∈ₛ x) i
    n ∈ₛ comm {x} {y} i = or-comm (n ∈ₛ x) (n ∈ₛ y) i
    n ∈ₛ idem {x} i = or-idem (n ∈ₛ x) i
    n ∈ₛ assoc· {x} {y} {z} i = {!!}
    n ∈ₛ rid· {x} i = (or-identityʳ _ ∙ and-identityʳ (n ∈ₛ x)) i
    n ∈ₛ comm· {x} {y} i = or-comm (n ∈ₛ x and not (0b? y)) (n ∈ₛ y and not (0b? x)) i
    n ∈ₛ def∅· {x} i = (or-identityʳ _ ∙ and-zeroʳ (n ∈ₛ x)) i
    n ∈ₛ dist {x} {y} {z} i = {!!}

    _P∈ₛ_ : ℕ → State → Type
    n P∈ₛ s = Bool→Type (n ∈ₛ s)

    _P∉ₛ_ : ℕ → State → Type
    n P∉ₛ s = ¬ (n P∈ₛ s)

    predₛ : ℕ → (q : State) → State
    predₛ n 0b = 0b
    predₛ n 1b = 1b
    predₛ n (`_ {l} x) = `_ {lpred[*> n ] l} x
    predₛ n (q1 ∪ q2) = predₛ n q1 ∪ predₛ n q2
    predₛ n (q1 · q2) = predₛ n q1 · predₛ n q2
    predₛ n (ν q) = ν (predₛ (suc n) q)
    predₛ n (ν-elim x i) = {!!}
    predₛ n (squash q q₁ x y i i₁) = {!!}
    predₛ n (assoc i) = {!!}
    predₛ n (rid i) = {!!}
    predₛ n (comm i) = {!!}
    predₛ n (idem i) = {!!}
    predₛ n (assoc· i) = {!!}
    predₛ n (rid· i) = {!!}
    predₛ n (comm· i) = {!!}
    predₛ n (def∅· i) = {!!}
    predₛ n (dist i) = {!!}

    l1 : ∀ n q → 0b? q ≡ 0b? (predₛ n q)
    l1 n 0b = refl
    l1 n 1b = refl
    l1 n (` x) = refl
    l1 n (q ∪ q₁) = cong₂ _and_ (l1 n q) (l1 n q₁)
    l1 n (q · q₁) = cong₂ _or_ (l1 n q) (l1 n q₁)
    l1 n (ν q) = l1 (suc n) q
    l1 n (ν-elim {q = q} x i) = toPathP (isSetBool _ _ (transp (λ i → 0b? (ν-elim {q = q} x i) ≡ 0b? (predₛ n (ν-elim {q = q} x i))) i0 (l1 (suc n) q)) (l1 n (predₛ 0 q))) i
    l1 n (squash q q₁ x y i i₁) = isOfHLevel→isOfHLevelDep 2 (λ w → isProp→isSet (isSetBool (0b? w) (0b? (predₛ n w)))) (l1 n q) (l1 n q₁) (cong (l1 n) x) (cong (l1 n) y) (squash q q₁ x y) i i₁
    l1 n (assoc {x} {y} {z} i) = toPathP (isSetBool _ _ (transp (λ i → 0b? (assoc {x} {y} {z} i) ≡ 0b? (predₛ n (assoc {x} {y} {z} i))) i0 (l1 n (x ∪ (y ∪ z)))) (l1 n ((x ∪ y) ∪ z)))  i
    l1 n (rid {x} i) = toPathP (isSetBool _ _ (transp (λ i → 0b? (rid {x} i) ≡ 0b? (predₛ n (rid {x} i))) i0 (l1 n (x ∪ 0b))) (l1 n x)) i
    l1 n (comm {x} {y} i) = toPathP (isSetBool _ _ (transp (λ i → 0b? (comm {x} {y} i) ≡ 0b? (predₛ n (comm {x} {y} i))) i0 (l1 n (x ∪ y))) (l1 n (y ∪ x))) i
    l1 n (idem {x} i) = toPathP (isSetBool _ _ (transp (λ i → 0b? (idem {x} i) ≡ 0b? (predₛ n (idem {x} i))) i0 (l1 n (x ∪ x))) (l1 n x)) i
    l1 n (assoc· {x} {y} {z} i) = toPathP (isSetBool _ _ (transp (λ i → 0b? (assoc· {x} {y} {z} i) ≡ 0b? (predₛ n (assoc· {x} {y} {z} i))) i0 (l1 n (x · (y · z)))) (l1 n ((x · y) · z)))  i
    l1 n (rid· {x} i) = toPathP (isSetBool _ _ (transp (λ i → 0b? (rid· {x} i) ≡ 0b? (predₛ n (rid· {x} i))) i0 (l1 n (x · 1b))) (l1 n x)) i
    l1 n (comm· {x} {y} i) = toPathP (isSetBool _ _ (transp (λ i → 0b? (comm· {x} {y} i) ≡ 0b? (predₛ n (comm· {x} {y} i))) i0 (l1 n (x · y))) (l1 n (y · x))) i
    l1 n (def∅· {x} i) = toPathP (isSetBool _ _ (transp (λ i → 0b? (def∅· {x} i) ≡ 0b? (predₛ n (def∅· {x} i))) i0 (l1 n (x · 0b))) (l1 n 0b)) i
    l1 n (dist {x} {y} {z} i) = toPathP (isSetBool _ _ (transp (λ i → 0b? (dist {x} {y} {z} i) ≡ 0b? (predₛ n (dist {x} {y} {z} i))) i0 (l1 n (x · (y ∪ z)))) (l1 n ((x · y) ∪  (x · z))))  i


    ∈ₛ-pred< : ∀ m n q → m P∈ₛ q → m ≤ n → m P∈ₛ predₛ n q
    ∈ₛ-pred< m n (`_ {l} x) e rel = ∈-pred<l m n l rel e
    ∈ₛ-pred< m n (q ∪ q₁) e rel with m ∈ₛ q | ∈ₛ-pred< m n q
    ... | true | ind = {!!}
    ... | false | ind = {!!}
    ∈ₛ-pred< m n (q · q₁) e rel = {!!}
    ∈ₛ-pred< m n (ν q) e rel = {!!}
    ∈ₛ-pred< m n (ν-elim x i) e rel = {!!}
    ∈ₛ-pred< m n (squash q q₁ x y i i₁) e rel = {!!}
    ∈ₛ-pred< m n (assoc i) e rel = {!!}
    ∈ₛ-pred< m n (rid i) e rel = {!!}
    ∈ₛ-pred< m n (comm i) e rel = {!!}
    ∈ₛ-pred< m n (idem i) e rel = {!!}
    ∈ₛ-pred< m n (assoc· i) e rel = {!!}
    ∈ₛ-pred< m n (rid· i) e rel = {!!}
    ∈ₛ-pred< m n (comm· i) e rel = {!!}
    ∈ₛ-pred< m n (def∅· i) e rel = {!!}
    ∈ₛ-pred< m n (dist i) e rel = {!!}


    ∈ₛ-pred-sucl : ∀ m n q → n < suc m → suc m P∈ₛ q → m P∈ₛ predₛ n q
    ∈ₛ-pred-sucl m n (` x) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (q ∪ q₁) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (q · q₁) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (ν q) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (ν-elim x i) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (squash q q₁ x y i i₁) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (assoc i) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (rid i) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (comm i) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (idem i) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (assoc· i) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (rid· i) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (comm· i) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (def∅· i) rel eqq = {!!}
    ∈ₛ-pred-sucl m n (dist i) rel eqq = {!!}

    ∈ₛ-pred-sucr : ∀ m n q → n < suc m → m P∈ₛ predₛ n q → suc m P∈ₛ q
    ∈ₛ-pred-sucr m n q rel eqq = {!!}

    predₛ-predₛ : ∀ n q → 0 P∉ₛ q → predₛ 0 (predₛ (suc n) q) ≡ predₛ n (predₛ 0 q)
    predₛ-predₛ = {!!}

  --   {-# TERMINATING #-}
  --   predₛ : ℕ → (q : State) → State
  --   predₛ n 0b = 0b
  --   predₛ n 1b = 1b
  --   predₛ n (`_ {l} x) = `_ {lpred[*> n ] l} x
  --   predₛ n (q1 ∪ q2) = predₛ n q1 ∪ predₛ n q2
  --   predₛ n (q1 · q2) = predₛ n q1 · predₛ n q2
  --   predₛ n (ν q) = ν (predₛ (suc n) q)
  --   predₛ n (ν-elim {q = q} x i) = (ν-elim (∉ₛ-pred 0 (suc n) q x (suc-≤-suc zero-≤)) ∙ wq n q x) i
  --   predₛ n (squash q q₁ x y i i₁) = squash (predₛ n q) (predₛ n q₁) (cong (predₛ n) x) (cong (predₛ n) y) i i₁
  --   predₛ n (assoc {x} {y} {z} i) = assoc {predₛ n x} {predₛ n y} {predₛ n z} i
  --   predₛ n (rid {x} i) = rid {predₛ n x} i
  --   predₛ n (comm i) = {!!}
  --   predₛ n (idem i) = {!!}
  --   predₛ n (assoc· i) = {!!}
  --   predₛ n (rid· i) = {!!}
  --   predₛ n (comm· i) = {!!}
  --   predₛ n (def∅· i) = {!!}
  --   predₛ n (dist i) = {!!}


  --   wq : ∀ n q → 0 ∉ₛ q → predₛ 0 (predₛ (suc n) q) ≡ predₛ n (predₛ 0 q)
  --   wq n 0b x = refl
  --   wq n 1b x = refl
  --   wq n (`_ {l} c) x = cong (λ e → `_ {e} c) (qq n l)
  --   wq n (q ∪ q₁) (0bc x) = {!!}
  --   wq n (q ∪ q₁) (1bc x) = {!!}
  --   wq n (q ∪ q₁) (`c x x₁) = {!!}
  --   wq n (q ∪ q₁) (∪c x x₁ x₂) = {!!}
  --   wq n (q ∪ q₁) (·c x x₁ x₂) = {!!}
  --   wq n (q ∪ q₁) (·lc x x₁) = {!!}
  --   wq n (q ∪ q₁) (·rc x x₁) = {!!}
  --   wq n (q ∪ q₁) (νc x x₁) = {!!}
  --   wq n (q · q₁) x = {!!}
  --   wq n (ν q) x = {!!}
  --   wq n (ν-elim x₁ i) x = {!!}
  --   wq n (squash q q₁ x₁ y i i₁) x = {!!}
  --   wq n (assoc i) x = {!!}
  --   wq n (rid i) x = {!!}
  --   wq n (comm i) x = {!!}
  --   wq n (idem i) x = {!!}
  --   wq n (assoc· i) x = {!!}
  --   wq n (rid· i) x = {!!}
  --   wq n (comm· i) x = {!!}
  --   wq n (def∅· i) x = {!!}
  --   wq n (dist i) x = {!!}
    
  --   ∉ₛ-pred : ∀ m n q → m ∉ₛ q → m < n → m ∉ₛ predₛ n q
  --   ∉ₛ-pred m n q (0bc x) rel = 0bc (J (λ y eq → Is0b y) 0bcc (sym (cong (predₛ n) (l1 _ x)))) where
  --     l1 : ∀ s → Is0b s → s ≡ 0b
  --     l1 .0b 0bcc = refl
  --     l1 .(_ · _) (·lcc {x} {c} e) = cong (λ x → x · c) (l1 x e) ∙ comm· ∙ def∅·
  --     l1 .(_ · _) (·rcc {x} {c} e) = cong (λ c → x · c) (l1 c e) ∙ def∅·
  --     l1 .(_ ∪ _) (∪cc e1 e2) = cong₂ _∪_ (l1 _ e1) (l1 _ e2) ∙ rid
  --   ∉ₛ-pred m n s (1bc e) rel = 1bc (cong (predₛ n) e)
  --   ∉ₛ-pred m n s (`c x e) rel = `c (ss x rel) (cong (predₛ n) e)

  -- --   ∉ₛ-pred m n s (x ∪c x₁) rel = _∪c_ (∉ₛ-pred m n _ x rel) ((∉ₛ-pred m n _ x₁ rel))
  -- --   ∉ₛ-pred m n .(_ · _) (x ·c x₁) rel = (∉ₛ-pred m n _ x rel) ·c (∉ₛ-pred m n _ x₁ rel)
  -- --   ∉ₛ-pred m n .(_ · _) (·lc x) rel = ·lc (J (λ y eq → Is0b y) 0bcc (sym (cong (predₛ n) (l1 _ x)))) where
  -- --     l1 : ∀ s → Is0b s → s ≡ 0b
  -- --     l1 .0b 0bcc = refl
  -- --     l1 .(_ · _) (·lcc {x} {c} e) = cong (λ x → x · c) (l1 x e) ∙ comm· ∙ def∅·
  -- --     l1 .(_ · _) (·rcc {x} {c} e) = cong (λ c → x · c) (l1 c e) ∙ def∅·
  -- --     l1 .(_ ∪ _) (∪cc e1 e2) = cong₂ _∪_ (l1 _ e1) (l1 _ e2) ∙ rid
  -- --   ∉ₛ-pred m n .(_ · _) (·rc x) rel = ·rc (J (λ y eq → Is0b y) 0bcc (sym (cong (predₛ n) (l1 _ x)))) where
  -- --     l1 : ∀ s → Is0b s → s ≡ 0b
  -- --     l1 .0b 0bcc = refl
  -- --     l1 .(_ · _) (·lcc {x} {c} e) = cong (λ x → x · c) (l1 x e) ∙ comm· ∙ def∅·
  -- --     l1 .(_ · _) (·rcc {x} {c} e) = cong (λ c → x · c) (l1 c e) ∙ def∅·
  -- --     l1 .(_ ∪ _) (∪cc e1 e2) = cong₂ _∪_ (l1 _ e1) (l1 _ e2) ∙ rid
  -- --   ∉ₛ-pred m n .(ν _) (νc_ {_} {s} x) rel = νc ∉ₛ-pred (suc m) (suc n) s x (suc-≤-suc rel)

  -- -- ff : ∀ s → Is0b s → s ≡ 0b
  -- -- ff .0b 0bcc = refl
  -- -- ff .(_ · _) (·lcc {x} {c} e) = cong (λ x → x · c) (ff x e) ∙ comm· ∙ def∅·
  -- -- ff .(_ · _) (·rcc {x} {c} e) = cong (λ c → x · c) (ff c e) ∙ def∅·
  -- -- ff .(_ ∪ _) (∪cc e1 e2) = cong₂ _∪_ (ff _ e1) (ff _ e2) ∙ rid


  

  -- -- F : State → State → Bool
  -- -- F 0b 0b = true
  -- -- F 0b 1b = false
  -- -- F 0b (` x) = false
  -- -- F 0b (s2 ∪ s3) = (F 0b s2) and (F 0b s3)
  -- -- F 0b (s2 · s3) = F 0b s2 or F 0b s3
  -- -- F 0b (ν s2) = {!!}
  -- -- F 0b (ν-elim x i) = {!!}
  -- -- F 0b (squash s2 s3 x y i i₁) = isSetBool (F 0b s2) (F 0b s3) (cong (F 0b) x) (cong (F 0b) y) i i₁
  -- -- F 0b (assoc {x} {y} {z} i) = and-assoc (F 0b x) (F 0b y) (F 0b z) i
  -- -- F 0b (rid {x} i) = and-identityʳ (F 0b x) i
  -- -- F 0b (comm {x} {y} i) = and-comm (F 0b x) (F 0b y) i
  -- -- F 0b (idem {x} i) = and-idem (F 0b x) i
  -- -- F 0b (assoc· {x} {y} {z} i) = or-assoc (F 0b x) (F 0b y) (F 0b z) i
  -- -- F 0b (rid· {x} i) = or-identityʳ (F 0b x) i
  -- -- F 0b (comm· {x} {y} i) = or-comm (F 0b x) (F 0b y) i
  -- -- F 0b (def∅· {x} i) = zeroʳ (F 0b x) i
  -- -- F 0b (dist {x} {y} {z} i) = or-and-dist (F 0b x) (F 0b y) (F 0b z) i
  -- -- F 1b 0b = false
  -- -- F 1b 1b = true
  -- -- F 1b (` x) = false
  -- -- F 1b (s2 ∪ s3) = (F 0b s2 and F 1b s3) or ((F 1b s2) and F 0b s3) or ((F 1b s2) and (F 1b s3))
  -- -- F 1b (s2 · s3) = F 1b s2 and F 1b s3
  -- -- F 1b (ν s2) = {!!}
  -- -- F 1b (ν-elim x i) = {!!}
  -- -- F 1b (squash s2 s3 x y i i₁) = isSetBool (F 1b s2) (F 1b s3) (cong (F 1b) x) (cong (F 1b) y) i i₁
  -- -- F 1b (assoc {x} {y} {z} i) with F 0b x | F 1b x | F 0b y | F 1b y | F 0b z | F 1b z
  -- -- ... | false | false | c | d | e | z = refl {x = false} i
  -- -- ... | false | true | false | d | e | z = refl {x =  d and e or d and z} i
  -- -- ... | false | true | true | false | e | z = cong (e or_) (or-identityʳ z) i
  -- -- ... | false | true | true | true | e | z = {!!}
  -- -- ... | true | false | false | false | e | z = refl {x = false} i
  -- -- ... | true | true | false | false | e | z = refl {x = false} i
  -- -- ... | true | false | false | true | e | z = {!!}
  -- -- ... | true | true | false | true | e | z = {!!}
  -- -- ... | true | false | true | false | false | false = refl {x = false} i
  -- -- ... | true | false | true | true | false | false = refl {x = false} i
  -- -- ... | true | false | true | d | true | false = refl {x = d} i
  -- -- ... | true | false | true | d | e | true = refl {x = true} i
  -- -- ... | true | true | true | false | e | false = refl {x = e or false} i
  -- -- ... | true | true | true | true | e | false = {!!}
  -- -- ... | true | true | true | d | e | true = refl {x = true} i
  -- -- F 1b (rid {x} i) with F 0b x | F 1b x
  -- -- ... | false | false = refl {x = false} i
  -- -- ... | false | true = refl {x = true} i
  -- -- ... | true | false = refl {x = false} i
  -- -- ... | true | true = refl {x = true} i
  -- -- F 1b (comm {x} {y} i) = {!!}
  -- -- F 1b (idem {x} i) with F 0b x | F 1b x
  -- -- ... | false | false = refl {x = false} i
  -- -- ... | false | true = refl {x = true} i
  -- -- ... | true | false = refl {x = false} i
  -- -- ... | true | true = refl {x = true} i
  -- -- F 1b (assoc· {x} {y} {z} i) = and-assoc (F 1b x) (F 1b y) (F 1b z) i
  -- -- F 1b (rid· {x} i) = and-identityʳ (F 1b x) i
  -- -- F 1b (comm· {x} {y} i) = and-comm (F 1b x) (F 1b y) i
  -- -- F 1b (def∅· {x} i) = and-zeroʳ (F 1b x) i
  -- -- F 1b (dist {x} {y} {z} i) = {!!}
  -- -- F (` x) s2 = {!!}
  -- -- F (s1 ∪ s3) s2 = {!!}
  -- -- F (s1 · s3) s2 = {!!}
  -- -- F (ν s1) s2 = {!!}
  -- -- F (ν-elim x i) s2 = {!!}
  -- -- F (squash s1 s3 x y i i₁) s2 = {!!}
  -- -- F (assoc i) s2 = {!!}
  -- -- F (rid i) s2 = {!!}
  -- -- F (comm i) s2 = {!!}
  -- -- F (idem i) s2 = {!!}
  -- -- F (assoc· i) s2 = {!!}
  -- -- F (rid· i) s2 = {!!}
  -- -- F (comm· i) s2 = {!!}
  -- -- F (def∅· i) s2 = {!!}
  -- -- F (dist i) s2 = {!!}


  -- -- gg : ∀ s → s ≡ 0b → ∥ Is0b s ∥₁
  -- -- gg 0b e = ∣ 0bcc ∣₁
  -- -- gg 1b e = {!!}
  -- -- gg (` x) e = {!!}
  -- -- gg (s ∪ s₁) e = {!!}
  -- -- gg (s · s₁) e = {!!}
  -- -- gg (ν s) e = {!!}
  -- -- gg (ν-elim x i) e = {!!}
  -- -- gg (squash s s₁ x y i i₁) e = {!!}
  -- -- gg (assoc i) e = {!!}
  -- -- gg (rid i) e = {!!}
  -- -- gg (comm i) e = {!!}
  -- -- gg (idem i) e = {!!}
  -- -- gg (assoc· i) e = {!!}
  -- -- gg (rid· i) e = {!!}
  -- -- gg (comm· i) e = {!!}
  -- -- gg (def∅· i) e = {!!}
  -- -- gg (dist i) e = {!!}
