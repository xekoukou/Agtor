
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Pointwise reducibility
/*
```agda
{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.FunExt

```
*/

```agda

open import PredP
open Pred
open Pred₂

module PW-Reducible (dfunext : ∀{𝓤 𝓥} → DN-funext 𝓤 𝓥) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) where

open import Definitions Msg Secret

open ΣPred

mΣ : <&PSet> 𝓥 𝓦 → _ ̇
mΣ p = Σ v ꞉ _ , p (v , ₀)

aΣ : <&PSet> 𝓥 𝓦 → _ ̇
aΣ p = Σ v ꞉ _ , p (v , ₁)

λaΣ : <&PSet> 𝓥 𝓦 → <BSet> (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
λaΣ &p x = Σ l ꞉ aΣ &p ,  < < l > > x 

λaΣ' : <&PSet> 𝓥 𝓦 → BSet (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦)
λaΣ' &p = (λaΣ &p) , λ ascrs scrs m (lt , mt) → (λ (l , cnd) → l , ((< l > str) ascrs scrs m (lt , mt) .pr₁ cnd)) , (λ (l , cnd) → l , ((< l > str) ascrs scrs m (lt , mt) .pr₂ cnd))

-- TODO It should be non-empty.
msg-reducible : <BSet> 𝓥 → <&PSet> 𝓥' 𝓦 → _ ̇
msg-reducible b &p
 = b ⇒ₚ λaΣ &p

¬msg-reducible : <BSet> 𝓥 → <&PSet> 𝓥' 𝓦 → _ ̇
¬msg-reducible b &p
 = Σ v ꞉ Σ b , ((l : aΣ &p) → ¬ < < l > > < v >)

&PSet-reducible→ : <&PSet> 𝓥 𝓦 → <&PSet> 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
&PSet-reducible→ a b = Σ l ꞉ mΣ a , msg-reducible < < l > > b

¬&PSet-reducible→ : <&PSet> 𝓥 𝓦 → <&PSet> 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
¬&PSet-reducible→ a b = (l : mΣ a) → ¬msg-reducible < < l > > b

&PSet-reducible : <&PSet> 𝓥 𝓦 → <&PSet> 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
&PSet-reducible a b = &PSet-reducible→ a b + &PSet-reducible→ b a

&PSet-PSet-reducible : <&PSet> 𝓥 𝓦 → <PSet> 𝓥' 𝓦' 𝓣' → _
&PSet-PSet-reducible &a pb = (&b : Σ pb) → &PSet-reducible &a < < &b > >

PSet-PSet-reducible : <PSet> 𝓥 𝓦 𝓣 → <PSet> 𝓥' 𝓦' 𝓣' → _
PSet-PSet-reducible pa pb = (&a : Σ pa) → &PSet-PSet-reducible < < &a > > pb

_⊑_ : <PSet> 𝓥 𝓦 𝓣 → <PSet> 𝓥' 𝓦' 𝓣' → 𝓤ω 
pa ⊑ pb = ∀{𝓥' 𝓦' 𝓣'} → (ctx : <PSet> 𝓥' 𝓦' 𝓣') → PSet-PSet-reducible pb ctx → PSet-PSet-reducible pa ctx

infix 2 _≼&_
_≼&_ : <&PSet> 𝓥 𝓦 → <&PSet> 𝓥' 𝓦' → _
&a ≼& &b = ((bsb : mΣ &b) → Σ bsa ꞉ mΣ &a , (< < bsa > > ⇒ₚ < < bsb > >)) × ((bsb : aΣ &b) → msg-reducible < < bsb > > &a)

_≼_ : <PSet> 𝓥 𝓦 𝓣 → <PSet> 𝓥' 𝓦' 𝓣' → _
a ≼ b = (&a : Σ a) → Σ &b ꞉ Σ b  , < < &a > > ≼& < < &b > >

-- TODO find a nice name for this.
bf : ∀{𝓥'' 𝓦''} → (&a : <&PSet> 𝓥 𝓦) → (&b : <&PSet> 𝓥' 𝓦') → (&c : <&PSet> 𝓥'' 𝓦'') → &a ≼& &b → &PSet-reducible &b &c → &PSet-reducible &a &c
bf &a &b &c (meq , aeq) (inl (mb , &pr→)) = let (ma , c) = meq mb in inl (ma , (λ m abs → &pr→ m (c m abs)))
bf &a &b &c (meq , aeq) (inr (mc , ←&pr)) = inr (mc , λ m cbs → let (bsb , rd) = ←&pr m cbs in aeq bsb m rd)

≼→⊑ : (a : <PSet> 𝓥 𝓦 𝓣) → (b : <PSet> 𝓥' 𝓦' 𝓣') → a ≼ b → a ⊑ b
≼→⊑ a b leq ctx ppr &a &c
 = let (&b , &a≼&b) = leq &a
       prbc = ppr &b &c
   in bf < < &a > >  < < &b > > < < &c > > &a≼&b prbc


_ᶜ : BSet 𝓥 × 𝟚 → BSet 𝓥 × 𝟚
(a , ₀) ᶜ = a , ₁
(a , ₁) ᶜ = a , ₀


a→←a-& : <&PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺) → <&PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺)
a→←a-& &pa (v , ₀) = &pa (v , ₀)
-- If <BSet> is a proposition, then due to Propositional extensionality,
-- we have an equality (we are in different universes???)
a→←a-& &pa (v , ₁) = < v > ⇔ₚ λaΣ &pa


a→←a : <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺) → <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺)
a→←a a &v = Σ &a ꞉ Σ a , < &v > ⇔ₚ a→←a-& < < &a > >


-- a choice function
-- it picks one BSet from each &PSet that belongs in PSet
Fun : <PSet> 𝓥 𝓦 𝓣 → _ ̇
Fun {𝓥 = 𝓥} {𝓦 = 𝓦} a
 = (&a : Σ a) → Σ < < &a > >


F⇒&P : {a : <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺)} → Fun a
       → <&PSet> 𝓥 (𝓤 ⁺ ⊔ 𝓥 ⁺⁺)
F⇒&P {a = a} f o = Σ &a ꞉ Σ a , < f &a > ＝₂ (o ᶜ)

_ᵀ : <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺) → <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺)
(a ᵀ) o =  let a→← = a→←a a in Σ f ꞉ Fun a→← , F⇒&P f ⇔ₚ < o >

a-aᵗ-red : (a : <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺)) → PSet-PSet-reducible a (a ᵀ)
a-aᵗ-red a Σ&a@(&a , &a∈a) Σ&aᵗ@(&aᵗ , &aᵗ∈aᵗ@(f , exeq))
-- Goal: &PSet-reducible <&a> <&aᵗ>
-- ————————————————————————————————————————————————————————————
-- Σ&aᵗ      : Σ (a ᵀ)
-- Σ&a       : Σ a
-- f         : Fun (a→←a a)
-- exeq      : F⇒&P f ⇔ₚ < &aᵗ >
 = Case bs-picked-from-&a→← of
    λ { (bs2@(bs , ₀) , bs∈&a→←a) eq →
          inl
   -- &PSet-reducible→ (<&a>) (<&aᵗ>)
          (((bs , bs∈&a→←a) ,
   -- msg-reducible <bs> <&aᵗ> 
        λ m m∈bs →
   --  aΣ <&aᵗ>
          (bs , exeq .pr₁ (bs , ₁) (Σ&a→← , ((ap (λ z → z .pr₁ .pr₂) eq) , ＝→⇐⇒ₚ _ _ (ap (λ z → z .pr₁ .pr₁ .pr₁) (eq ⁻¹))))) , m∈bs))
      ; ((bs , ₁) , bs∈&a→←) eq →
         inr
   -- &PSet-reducible→ (&aᵗ .pr₁) (&a .pr₁)
      ((bs , exeq .pr₁ (bs , ₀) (Σ&a→← , (((ap (λ z → z .pr₁ .pr₂) eq) , ＝→⇐⇒ₚ _ _ (ap (λ z → z .pr₁ .pr₁ .pr₁) (eq ⁻¹)))))) ,
  -- msg-reducible (bs .pr₁) (&a .pr₁)
      λ m m∈bs → bs∈&a→← .pr₁ m m∈bs)
      } where
 open Pred₂'
 &a→← = a→←a-& < &a >
 &a→←∈a→← : a→←a a (&a→← , ⋆)
 &a→←∈a→← = Σ&a , ((λ v z → z) , (λ v z → z))
 Σ&a→← = (&a→← , ⋆) , &a→←∈a→←
 bs-picked-from-&a→← = f Σ&a→←
 bs-with-eq : Σ (λ x → x ＝ f Σ&a→←)
 bs-with-eq = bs-picked-from-&a→← , refl

-- We need to construct a BSet in the same universe.
Cond : (a : <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺) 𝓣) → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓣 ̇
Cond {𝓥 = 𝓥} a = ∀ (&a : Σ a) → Σ v ꞉ BSet 𝓥 , < v > ⇔ₚ λaΣ < < &a > >

Condf : (a : <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺)) → _
Condf {𝓥 = 𝓥} a = (f : Fun a) → Σ p ꞉ &PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺) , F⇒&P f ⇔ₚ < p >

cb-red⇒c≼bᵀ : (a b : <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺)) → Cond a → Condf (a→←a a) → PSet-PSet-reducible a b → b ≼ (a ᵀ)
cb-red⇒c≼bᵀ {𝓥 = 𝓥} a b cond condf red-a-b &b = &aᵀ , d , d2 where
 a→← = a→←a a
 G : (&a→← : Σ a→←) → (k : (Σ < < &a→← > >)) → 𝓤 ⊔ 𝓥 ⁺ ̇
 G &a→← ((e , ₁) , v) = Σ bs ꞉ mΣ < < &b > > , msg-reducible < < bs > > < < < &a→← .pr₂ > > >
 G &a→← ((e , ₀) , v) = msg-reducible < e > < < &b > >
 f : (&a→← : Σ a→←) → Σ (G &a→←)
 f &a→← = l2 l1 where
  &v = < &a→← >
  &a = < &a→← .pr₂ >
  &v⇔ₚa→←a-&a = &a→← .pr₂ .pr₂
  l1 : &PSet-reducible < < &a > > < < &b > >
  l1 = red-a-b &a &b
  l2 : &PSet-reducible < < &a > > < < &b > > → _
  l2 (inl (mΣ&a@(bs , bs₀∈&a) , ms-red)) = ((bs , ₀) , &v⇔ₚa→←a-&a .pr₂ _ bs₀∈&a) , ms-red
  l2 (inr (mΣ&b@(bs , bs₀∈&b) , ms-red)) = ((cond &a .pr₁ , ₁) ,  &v⇔ₚa→←a-&a .pr₂ _ h) , ((bs , bs₀∈&b) , ms-red) where
   h : a→←a-& < < &a > > (cond &a .pr₁ , ₁ )
   h = cond &a .pr₂
 &aᵀ : Σ (a ᵀ)
 &aᵀ = condf (λ &a→← → f &a→← .pr₁) .pr₁ , (λ &a→← → f &a→← .pr₁) , condf (λ &a→← → f &a→← .pr₁) .pr₂ 
 d : (bsa : mΣ < < &aᵀ > >) →
      Σ bsb ꞉ mΣ < < &b > > , < < bsb > > ⇒ₚ < < bsa > >
 d q@(bs , bs₀∈p) = h where
 -- I used "F⇒&P f ⇔ₚ < o >" to get that
  <f> = (λ &a→← → f &a→← .pr₁)
  bs₀∈F⇒&Pf : F⇒&P <f> (bs , ₀)
  bs₀∈F⇒&Pf = condf (λ &a→← → f &a→← .pr₁) .pr₂ .pr₂ (bs , ₀) bs₀∈p
  <f>V : Σ (a→←a a)
  <f>V = bs₀∈F⇒&Pf .pr₁
  V = < <f>V >
  V∈a→←a-a : a→←a a V
  V∈a→←a-a = <f>V .pr₂
  Σ&a = V∈a→←a-a .pr₁
  V⇔ₚa→←a-&-&a : < V > ⇔ₚ a→←a-& < < Σ&a > >
  V⇔ₚa→←a-&-&a = V∈a→←a-a .pr₂
  k = < <f> <f>V >
  k∈V : < V > k
  k∈V = <f> <f>V .pr₂
  <fV⇒>=bs₁ : k ＝₂ (bs , ₁) 
  <fV⇒>=bs₁ = bs₀∈F⇒&Pf .pr₂
  l : ∀ k → k ＝ < <f> <f>V > → (k∈V : < V > k) → k ＝₂ (bs , ₁) → G <f>V (k , k∈V) → Sigma (mΣ < < &b > >) (λ bsb → < < bsb > > ⇒ₚ < < q > >)
  l (k , ₁) eq k∈V (refl , eq2) (bmΣ , g) = bmΣ , we where
   we : < < bmΣ > > ⇒ₚ < bs >
   we msg ww = eq2 .pr₂ msg (l2 .pr₂ msg l1) where
    l1 : λaΣ < < Σ&a > > msg
    l1 = g msg ww
    vλ : _
    vλ = cond Σ&a .pr₁
    msg∈vλ = cond Σ&a .pr₂ .pr₂ msg l1
    l2 : < k > ⇔ₚ λaΣ < < Σ&a > >
    l2 = V⇔ₚa→←a-&-&a .pr₁ (k , ₁) k∈V
   
  h = l k refl k∈V <fV⇒>=bs₁ (f <f>V .pr₂)
 d2 : (bsa : aΣ < < &aᵀ > >) → msg-reducible < < bsa > > < < &b > >
 d2 q@(bs , bs₁∈p) = h where
  <f> = (λ &a→← → f &a→← .pr₁)
  bs₀∈F⇒&Pf : F⇒&P <f> (bs , ₁)
  bs₀∈F⇒&Pf = condf (λ &a→← → f &a→← .pr₁) .pr₂ .pr₂ (bs , ₁) bs₁∈p
  <f>V : Σ (a→←a a)
  <f>V = bs₀∈F⇒&Pf .pr₁
  V = < <f>V >
  V∈a→←a-a : a→←a a V
  V∈a→←a-a = <f>V .pr₂
  Σ&a = V∈a→←a-a .pr₁
  V⇔ₚa→←a-&-&a : < V > ⇔ₚ a→←a-& < < Σ&a > >
  V⇔ₚa→←a-&-&a = V∈a→←a-a .pr₂
  k = < <f> <f>V >
  k∈V : < V > k
  k∈V = <f> <f>V .pr₂
  <fV⇒>=bs₁ : k ＝₂ (bs , ₀) 
  <fV⇒>=bs₁ = bs₀∈F⇒&Pf .pr₂
  l : ∀ k → k ＝ < <f> <f>V > → (k∈V : < V > k) → k ＝₂ (bs , ₀) → G <f>V (k , k∈V) → msg-reducible < < q > > < < &b > >
  l (k , ₀) eq k∈V (refl , eq2) g = we where
   we : (msg : S×Msg) → < bs > msg → λaΣ < < &b > > msg
   we = λ msg z → g msg (eq2 .pr₁ msg z)

  h = l k refl k∈V <fV⇒>=bs₁ (f <f>V .pr₂)
