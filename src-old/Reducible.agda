{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import UF.Univalence
open import UF.Equiv
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Base
open import UF.UniverseEmbedding

open import Lists

module Reducible (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) where

open PropositionalTruncation pt
open import UF.ImageAndSurjection pt

variable
 A : 𝓤 ̇

Pred : (A : 𝓤 ̇ ) → ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
Pred A 𝓥 = ((v : A) → 𝓥 ̇ )

infix 2 _⇒_
_⇒_ : {A : 𝓤 ̇ } → Pred A 𝓥 → Pred A 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
a ⇒ b = ∀ v → a v → b v

-- same as Sigma ??
Σv : Pred A 𝓥 → _ ̇
Σv p = Σ v ꞉ _ , p v

infix 3 _val

_val : {X : Pred A 𝓥} → Σv X → A
σv val = σv .pr₁

mΣv : Pred (𝟚 × A) 𝓥 → _ ̇
mΣv p = Σ v ꞉ _ , p (₀ , v)

aΣv : Pred (𝟚 × A) 𝓥 → _ ̇
aΣv p = Σ v ꞉ _ , p (₁ , v)

module _ (A : 𝓤 ̇) where

 ×BSet : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
 ×BSet 𝓥 = Pred A 𝓥

 &PSet : ∀ 𝓥 𝓦 → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
 &PSet 𝓥 𝓦 = Pred (𝟚 × ×BSet 𝓥) 𝓦

 PSet : ∀ 𝓥 𝓦 𝓣 → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇
 PSet 𝓥 𝓦 𝓣 = Pred (&PSet 𝓥 𝓦 × &PSet 𝓥 𝓦) 𝓣

 msg-reducible : ×BSet 𝓥 → &PSet 𝓥' 𝓦 → _ ̇
 msg-reducible b &p
  = ∀ x → b x → Σ l ꞉ aΣv &p , (l val) x

 ¬msg-reducible : ×BSet 𝓥 → &PSet 𝓥' 𝓦 → _ ̇
 ¬msg-reducible b &p
  = Σ v ꞉ Σ b , ((l : aΣv &p) → ¬ (l val) (v val))

-- cumulativity of universes ????
 ¬msg-red-g-cum : {b : ×BSet 𝓥} → {&p : &PSet 𝓥' 𝓦} → ¬msg-reducible b &p → ¬msg-reducible b (λ v → &p v × 𝟙 {𝓦'})
 ¬msg-red-g-cum {b = b} {&p} (v , c) = v , (λ l x → c (l .pr₁ , l .pr₂ .pr₁) x)

-- cumulativity of universes ????
 ¬msg-red-g-cum2 : {b : ×BSet 𝓥} → {&p : &PSet 𝓥' 𝓦} → ¬msg-reducible b (λ v → &p v × 𝟙 {𝓦'}) → ¬msg-reducible b &p
 ¬msg-red-g-cum2 {b = b} {&p} (v , c) = v , λ l x → c (l .pr₁ , l .pr₂ , _ ) x

 &PSet-reducible→ : &PSet 𝓥 𝓦 → &PSet 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
 &PSet-reducible→ a b = Σ l ꞉ mΣv a , msg-reducible (l val) b

 ¬&PSet-reducible→ : &PSet 𝓥 𝓦 → &PSet 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
 ¬&PSet-reducible→ a b = (l : mΣv a) → ¬msg-reducible (l val) b

-- cumulativity of universes ????
 ¬&PSet-reducible→cum : {&a : &PSet 𝓥 𝓦} → {&b : &PSet 𝓥' 𝓦'} → ¬&PSet-reducible→ &a &b → ¬&PSet-reducible→ ((λ v → &a v × 𝟙 {𝓣})) (λ v → &b v × 𝟙 {𝓣'})
 ¬&PSet-reducible→cum {&a = &a} {&b} c l = ¬msg-red-g-cum {&p = &b} (c (l .pr₁ , l .pr₂ .pr₁))

 ¬&PSet-reducible→cum2 : {&a : &PSet 𝓥 𝓦} → {&b : &PSet 𝓥' 𝓦'} → ¬&PSet-reducible→ ((λ v → &a v × 𝟙 {𝓣})) (λ v → &b v × 𝟙 {𝓣'}) → ¬&PSet-reducible→ &a &b
 ¬&PSet-reducible→cum2 {&a = &a} {&b} x l = ¬msg-red-g-cum2 {&p = &b} (x (l .pr₁ , l .pr₂ , _))

 ¬&PS-red⇒¬ : (&pa : &PSet 𝓥 𝓦) → (&pb : &PSet 𝓥' 𝓦')
              → ¬&PSet-reducible→ &pa &pb → ¬ &PSet-reducible→ &pa &pb
 ¬&PS-red⇒¬ pa pb ¬c (v , c) = let e  = ¬c v
                                   m = e .pr₁
                                   cc = c (m .pr₁) (m .pr₂)
                                   a = cc .pr₁
                                   v = cc .pr₂
                                in e .pr₂ a v

 &PSet-reducible : &PSet 𝓥 𝓦 → &PSet 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
 &PSet-reducible a b = &PSet-reducible→ a b + &PSet-reducible→ b a

 PSet-PSet-reducible-fiber : (&PSet 𝓥 𝓦 × &PSet 𝓥 𝓦) → (&PSet 𝓥' 𝓦' × &PSet 𝓥' 𝓦')
                             → _
 PSet-PSet-reducible-fiber &a@(&pa , &ica) &b@(&pb , &icb)
  = &PSet-reducible &pa &pb + &PSet-reducible &ica &ica + &PSet-reducible &icb &icb

 PSet-PSet-reducible : PSet 𝓥 𝓦 𝓣 → PSet 𝓥' 𝓦' 𝓣' → _
 PSet-PSet-reducible pa pb = (&a : Σ pa) → ¬&PSet-reducible→ (&a .pr₁ .pr₂) (&a .pr₁ .pr₂) → (&b : Σ pb) → ¬&PSet-reducible→ (&b .pr₁ .pr₂) (&b .pr₁ .pr₂) → &PSet-reducible (&a .pr₁ .pr₁) (&b .pr₁ .pr₁)

 _⊑_ : PSet 𝓥 𝓦 𝓣 → PSet 𝓥' 𝓦' 𝓣' → 𝓤ω 
 pa ⊑ pb = ∀{𝓥' 𝓦' 𝓣'} → (ctx : PSet 𝓥' 𝓦' 𝓣') → PSet-PSet-reducible pb ctx → PSet-PSet-reducible pa ctx

 -- less means stricter rules
 -- more means more relaxed rules

 infix 2 _≼&_
 _≼&_ : &PSet 𝓥 𝓦 → &PSet 𝓥' 𝓦' → _
 &a ≼& &b = ((bsb : mΣv &b) → Σ bsa ꞉ mΣv &a , (bsa val ⇒ bsb val)) × ((bsb : aΣv &b) → msg-reducible (bsb val) &a)

 _≼_ : PSet 𝓥 𝓦 𝓣 → PSet 𝓥' 𝓦' 𝓣' → _
 a ≼ b = (&ac : (Σ &a ꞉ Σ a , ¬&PSet-reducible→ (&a .pr₁ .pr₂) (&a .pr₁ .pr₂))) → Σ &bc ꞉ (Σ &b ꞉ Σ b , ¬&PSet-reducible→ (&b .pr₁ .pr₂) (&b .pr₁ .pr₂)) , &ac .pr₁ .pr₁ .pr₁ ≼& &bc .pr₁ .pr₁ .pr₁

 ≼→⊑ : (a : PSet 𝓥 𝓦 𝓣) → (b : PSet 𝓥' 𝓦' 𝓣') → a ≼ b → a ⊑ b
 ≼→⊑ a b rel ctx bc-red &a ¬sreda &c ¬redc
  = let (&bc , (c1 , c2)) = rel (&a , ¬sreda)
        &pb = &bc .pr₁ .pr₁
        v = bc-red (&bc .pr₁) (&bc .pr₂) &c ¬redc
    in case v of
       λ { (inl (bsb , m-c)) → inl let (bsa , ca) = c1 bsb in
                                       bsa , λ m m∈ → m-c m (ca m m∈)
         ; (inr (bsc , m-c)) → inr (bsc , λ m m∈ → let bsb = m-c m m∈
                                                       w = c2 (bsb .pr₁) m (bsb .pr₂)
                                                   in w)}


 a→←a-& : &PSet 𝓥 𝓦 → &PSet (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺)
 a→←a-& {𝓥 = 𝓥} {𝓦} &pa (₀ , v) = Σ q ꞉ mΣv &pa , v ＝ λ x → Lift (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) (q .pr₁ x)
 a→←a-& &pa (₁ , v) = v ＝ λ x → Σ l ꞉ aΣv &pa , (l val) x

-- we indtroduce 𝟘 in vi immediately here, to simplify things!! ?!
 a→←a : PSet 𝓥 𝓦 𝓣 → PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺) (𝓤 ⁺⁺ ⊔ 𝓥 ⁺⁺ ⁺ ⊔ 𝓦 ⁺⁺ ⊔ 𝓣)
 a→←a {𝓥 = 𝓥} {𝓦} a (v , vi)
  = Σ &a ꞉ Σ a ,
     let &pa = &a .pr₁ .pr₁
         &ia = &a .pr₁ .pr₂
     in (¬&PSet-reducible→ &ia &ia) × ((v ＝ a→←a-& &pa)
        × (vi ＝ λ _ → 𝟘))


 _ᶜ : 𝟚 × ×BSet 𝓥 → 𝟚 × ×BSet 𝓥
 (₀ , a) ᶜ = ₁ , a
 (₁ , a) ᶜ = ₀ , a

 Fun : PSet 𝓥 𝓦 𝓣 → _ ̇
 Fun {𝓥 = 𝓥} {𝓦 = 𝓦} a
  = (&a : Σ a) → let &pa = &a .pr₁ .pr₁
                 in Σ bs ꞉ _ , &pa (bs ᶜ)

 FunG : (G : 𝟚 × ×BSet 𝓥 → 𝓣' ̇) → PSet 𝓥 𝓦 𝓣 → _ ̇
 FunG {𝓥 = 𝓥} {𝓦 = 𝓦} G a
  = (&a : Σ a) → let &pa = &a .pr₁ .pr₁
                 in Σ bs ꞉ _ , &pa (bs ᶜ) × G bs


 F⇒&P : {p : PSet 𝓥 𝓦 𝓣} → Fun p
        → &PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣)
 F⇒&P {p = p} f o = Σ q ꞉ _ , f q .pr₁ ＝ o

 FunG⇒Fun : {G : 𝟚 × ×BSet 𝓥 → 𝓣' ̇} → {p : PSet 𝓥 𝓦 𝓣} → FunG G p → Fun p
 FunG⇒Fun f q = f q .pr₁ , f q .pr₂ .pr₁

 FunG⇒Fun×Pr : {G : 𝟚 × ×BSet 𝓥 → 𝓣' ̇} → {p : PSet 𝓥 𝓦 𝓣} → FunG G p
               → Σ f ꞉ Fun p , ((o : Σ (F⇒&P f)) → G (o .pr₁))
 FunG⇒Fun×Pr {G = G} fg = (λ q → fg q .pr₁ , fg q .pr₂ .pr₁) , l1 where
  l1 : (o : Σ (F⇒&P (λ q → fg q .pr₁ , fg q .pr₂ .pr₁))) → G (o .pr₁)
  l1 (o , d , refl) = fg d .pr₂ .pr₂

 _ᵀ : PSet 𝓥 𝓦 𝓣 → PSet (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) (𝓤 ⁺⁺ ⊔ 𝓥 ⁺⁺ ⁺ ⊔ 𝓦 ⁺⁺ ⊔ 𝓣) (𝓤 ⁺⁺ ⁺ ⊔ 𝓥 ⁺⁺ ⁺⁺ ⊔ 𝓦 ⁺⁺ ⁺ ⊔ 𝓣 ⁺)
 (p ᵀ) o = Σ q ꞉ Fun (a→←a p) , (F⇒&P q , λ _ → 𝟘) ＝ o

 private
  D : {p : PSet 𝓥 𝓦 𝓣} → _ → Fun p → _
  D q f = Σ λ x → f q ＝ x


 a-aᵗ-red : (a : PSet 𝓥 𝓦 𝓣) → PSet-PSet-reducible a (a ᵀ)
 a-aᵗ-red {𝓥 = 𝓥} {𝓦} a &a ¬sred (&aᵗ , f , refl) _ = l1 bs bsᶜ∈&pa→← refl where
  &pa = &a .pr₁ .pr₁
  &pa→← = a→←a-& &pa
  &ia = &a .pr₁ .pr₂
  a→←a∈ : Σ (a→←a a)
  a→←a∈ = (&pa→← , (λ _ → 𝟘)) , &a , ¬sred , refl , refl
  r = f a→←a∈
  bs : 𝟚 × ×BSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
  bs = r .pr₁
  bsᶜ∈&pa→← : &pa→← (bs ᶜ)
  bsᶜ∈&pa→← = r .pr₂
  l1 : ∀ bs → (c : &pa→← (bs ᶜ)) → (bs , c) ＝ r → &PSet-reducible &pa (&aᵗ .pr₁)
  l1 (₀ , bs) refl eq = inr ((bs , a→←a∈ , ap pr₁ (eq ⁻¹)) , λ x z → z)
  l1 (₁ , bs) (q , refl) eq = inl (((q .pr₁) , (q .pr₂)) , λ x v → (bs , a→←a∈ , ap pr₁ (eq ⁻¹)) , (v , _))

 cb-red⇒c≼bᵀ : (b : PSet 𝓥 𝓦 𝓣) → (a : PSet 𝓥 𝓦 𝓣) → PSet-PSet-reducible b a → b ≼ (a ᵀ)
 cb-red⇒c≼bᵀ {𝓥 = 𝓥} {𝓦} b a b-a-red (&b , ¬redb)
  =   (((F⇒&P f , (λ v → 𝟘)) , f , refl) , λ ())
    , l2 where
  c = b-a-red &b ¬redb
  &pb = &b .pr₁ .pr₁
  cond : 𝟚 × ×BSet _ → _
  cond (₀ , bs) = Σ bsa ꞉ mΣv &pb , (bsa val ⇒ bs)
  cond (₁ , bs) = msg-reducible bs &pb
  fung : FunG cond (a→←a a)
  fung (d , (&a , ¬reda , refl , refl)) = let q = c &a ¬reda in l1 q where
    l1 : &PSet-reducible (&b .pr₁ .pr₁) (&a .pr₁ .pr₁) → _
    l1 (inl x) = (₀ , (λ v → Sigma (aΣv (&a .pr₁ .pr₁)) (λ l → (l val) v))) ,
                  refl , x
    l1 (inr (e , v)) = (₁ ,  λ x → Lift (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) (e .pr₁ x)) , (e , refl) , λ x z → v x (z .pr₁)
  fun = FunG⇒Fun×Pr fung
  f = fun .pr₁
  co = fun .pr₂
  l2 : &b .pr₁ .pr₁ ≼& F⇒&P f
  l2 .pr₁ (bs , bs∈F⇒&P) = let q = co ((₀ , bs) , bs∈F⇒&P) in q
  l2 .pr₂ (bs , bs∈F⇒&P) = let q = co ((₁ , bs) , bs∈F⇒&P) in q

