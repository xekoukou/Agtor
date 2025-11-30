
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Pointwise reducibility
/*
```agda
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
mΣ p = Σ v ꞉ _ , p (₀ , v)

aΣ : <&PSet> 𝓥 𝓦 → _ ̇
aΣ p = Σ v ꞉ _ , p (₁ , v)

msg-reducible : <BSet> 𝓥 → <&PSet> 𝓥' 𝓦 → _ ̇
msg-reducible b &p
 = ∀ x → b x → Σ l ꞉ aΣ &p ,  < < l > > x 

¬msg-reducible : <BSet> 𝓥 → <&PSet> 𝓥' 𝓦 → _ ̇
¬msg-reducible b &p
 = Σ v ꞉ Σ b , ((l : aΣ &p) → ¬ < < l > > < v >)

&PSet-reducible→ : <&PSet> 𝓥 𝓦 → <&PSet> 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
&PSet-reducible→ a b = Σ l ꞉ mΣ a , msg-reducible < < l > > b

¬&PSet-reducible→ : <&PSet> 𝓥 𝓦 → <&PSet> 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
¬&PSet-reducible→ a b = (l : mΣ a) → ¬msg-reducible < < l > > b

&PSet-reducible : <&PSet> 𝓥 𝓦 → <&PSet> 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
&PSet-reducible a b = &PSet-reducible→ a b + &PSet-reducible→ b a

PSet-PSet-reducible : <PSet> 𝓥 𝓦 𝓣 → <PSet> 𝓥' 𝓦' 𝓣' → _
PSet-PSet-reducible pa pb = (&a : Σ pa) → (&b : Σ pb) → &PSet-reducible < < &a > > < < &b > >

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


_ᶜ : 𝟚 × BSet 𝓥 → 𝟚 × BSet 𝓥
(₀ , a) ᶜ = ₁ , a
(₁ , a) ᶜ = ₀ , a

-- This is a simpler version to the one in src-old. I am not sure I need the more general one.

_ᵀ : <&PSet> 𝓥 𝓦 → <PSet> 𝓥 𝓦 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
(p ᵀ) o = Σ bs ꞉ Σ p , < o > (< bs > ᶜ)
