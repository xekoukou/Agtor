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

open import Lists

module Reducible2 (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) where

open PropositionalTruncation pt
open import UF.ImageAndSurjection pt


variable
 A : 𝓤 ̇

Pred : (A : 𝓤 ̇ ) → ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
Pred A 𝓥 = ((v : A) → 𝓥 ̇ )

Σv : Pred A 𝓥 → _ ̇
Σv p = Σ v ꞉ _ , p v

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

 ESet : ∀ 𝓥 𝓦 𝓣 → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇
 ESet 𝓥 𝓦 𝓣 = Pred (&PSet 𝓥 𝓦) 𝓣

 PSet : ∀ 𝓥 𝓦 𝓣 → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇
 PSet 𝓥 𝓦 𝓣 = Pred (&PSet 𝓥 𝓦 × &PSet 𝓥 𝓦) 𝓣

 msg-reducible-g : ×BSet 𝓥 → Pred (𝟚 × ×BSet 𝓥') 𝓦 → _ ̇
 msg-reducible-g b &p
  = ∀ x → b x → Σ l ꞉ aΣv &p , (l val) x

 &PSet-reducible→ : &PSet 𝓥 𝓦 → &PSet 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
 &PSet-reducible→ a b = Σ l ꞉ mΣv a , msg-reducible-g (l val) b

 &PSet-reducible : &PSet 𝓥 𝓦 → &PSet 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
 &PSet-reducible a b = &PSet-reducible→ a b + &PSet-reducible→ b a


 ESet-reducible-fiber : &PSet 𝓥 𝓦 → ESet 𝓥' 𝓦' 𝓣' → _
 ESet-reducible-fiber &pa pb = ∀ &pb → pb &pb → &PSet-reducible &pa &pb

 -- Here we ingore the internal reduction alltogether.
 -- ESet reduction means that we can prove that in all cases, it can
 -- reduce enxternally

 ESet-reducible : ESet 𝓥 𝓦 𝓣 → ESet 𝓥' 𝓦' 𝓣' → _
 ESet-reducible pa pb = ∀ &pa → pa &pa → ESet-reducible-fiber &pa pb

 -- -- Here we ingore the external reduction alltogether.
 -- -- ESet reduction means that we can prove that in all cases, it can
 -- -- reduce internally
 
 -- -- Since we are talking about the same system,
 -- -- a system can only exist in one superposition.
 Self-reducible : ESet 𝓥 𝓦 𝓣 → _
 Self-reducible pa = ∀ &pa → pa &pa → &PSet-reducible &pa &pa


 PSet-ctx-reducible-fiber : (&PSet 𝓥 𝓦) × (&PSet 𝓥 𝓦) → ESet 𝓥' 𝓦' 𝓣' → _
 PSet-ctx-reducible-fiber (&pa , &ic) ctx = ESet-reducible-fiber &pa ctx + &PSet-reducible &ic &ic 

 PSet-ctx-reducible :  PSet 𝓥 𝓦 𝓣 → ESet 𝓥' 𝓦' 𝓣' → _ ̇
 PSet-ctx-reducible pa ctx = ∀ &pa &ic → pa (&pa , &ic) → PSet-ctx-reducible-fiber (&pa , &ic) ctx

 _toCtx : PSet 𝓥 𝓦 𝓣 → Pred (&PSet 𝓥 𝓦) _
 (pa toCtx) o = Σ λ &ps → pa (o , &ps)


 _toInt : PSet 𝓥 𝓦 𝓣 → Pred (&PSet 𝓥 𝓦) _
 (pa toInt) o = Σ λ &ps → pa (&ps , o)


 PSet-PSet-reducible-fiber : (&PSet 𝓥 𝓦 × &PSet 𝓥 𝓦) → (&PSet 𝓥' 𝓦' × &PSet 𝓥' 𝓦')
                             → _
 PSet-PSet-reducible-fiber &a@(&pa , &ica) &b@(&pb , &icb)
  = &PSet-reducible &pa &pb + &PSet-reducible &ica &ica + &PSet-reducible &icb &icb

 PSet-PSet-reducible : PSet 𝓥 𝓦 𝓣 → PSet 𝓥' 𝓦' 𝓣' → _
 PSet-PSet-reducible pa pb = ∀ &pa &ica → pa (&pa , &ica) → ∀ &pb &icb → pb (&pb , &icb) → PSet-PSet-reducible-fiber (&pa , &ica) (&pb , &icb)


 _⊑_ : PSet 𝓥 𝓦 𝓣 → PSet 𝓥' 𝓦' 𝓣' → 𝓤ω 
 pa ⊑ pb = ∀{𝓥' 𝓦' 𝓣'} → (ctx : Pred (Pred (𝟚 × Pred _ 𝓥') 𝓦') 𝓣') → PSet-ctx-reducible pb ctx → PSet-ctx-reducible pa ctx 

 _ᶜ : 𝟚 × ×BSet 𝓥 → 𝟚 × ×BSet 𝓥
 (₀ , a) ᶜ = ₁ , a
 (₁ , a) ᶜ = ₀ , a

 Fun : ESet 𝓥 𝓦 𝓣 → _ ̇
 Fun {𝓥 = 𝓥} {𝓦 = 𝓦} p = (q : Σv p) → Σ bs ꞉ (𝟚 × ×BSet 𝓥) , (q val) (bs ᶜ)

 F⇒&P : {p : ESet 𝓥 𝓦 𝓣} → Fun p
        → Pred (𝟚 × ×BSet 𝓥) (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣)
 F⇒&P {p = p} f o = Σ q ꞉ Σv p , f q .pr₁ ＝ o
 
 _ᵀ : ESet 𝓥 𝓦 𝓣 → ESet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺⁺ ⊔ 𝓣 ⁺)
 (p ᵀ) o = Σ q ꞉ Fun p , F⇒&P q ＝ o

 Fun' : PSet 𝓥 𝓦 𝓣 → _ ̇
 Fun' {𝓥 = 𝓥} {𝓦 = 𝓦} p = (q : Σ t ꞉ _ , p t × (¬ &PSet-reducible (t .pr₂) (t .pr₂))) → Σ bs ꞉ _ , q .pr₁ .pr₁ (bs ᶜ)

 F⇒&P' : {p : PSet 𝓥 𝓦 𝓣} → Fun' p
        → &PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣)
 F⇒&P' {p = p} f o = Σ q ꞉ _ , f q .pr₁ ＝ o
 
 _ᵀ' : PSet 𝓥 𝓦 𝓣 → ESet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺⁺ ⊔ 𝓣 ⁺)
 (p ᵀ') o = Σ q ꞉ Fun' p , F⇒&P' q ＝ o

 theorem : (a : PSet 𝓥 𝓦 𝓣) → (b : PSet 𝓥' 𝓦' 𝓣') → PSet-ctx-reducible a (b ᵀ') → a ⊑ b
 theorem a b abt-red ctx bc-red &ap &ai pi∈a with abt-red &ap &ai pi∈a
 ... | inr r = inr r
 -- ap fiber
 ... | inl abt-fib = {!!} where
  l1 : ∀ &pc → ctx &pc → Fun' b
  l1 &pc &pc∈ctx ((&pb , &ic), (&pb∈b , ¬selfb)) with bc-red &pb &ic &pb∈b
  -- &pb fiber
  ... | inr r = 𝟘-elim (¬selfb r)
  ... | inl bc-fib with bc-fib &pc &pc∈ctx
  ... | inl x = {!!}
  ... | inr x = {!!}
