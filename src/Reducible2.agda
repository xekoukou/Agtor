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

-- same as Sigma ??
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

 msg-reducible-g : ×BSet 𝓥 → &PSet 𝓥' 𝓦 → _ ̇
 msg-reducible-g b &p
  = ∀ x → b x → Σ l ꞉ aΣv &p , (l val) x

 ∥msg-reducible-g∥ : ×BSet 𝓥 → &PSet 𝓥' 𝓦 → _ ̇
 ∥msg-reducible-g∥ b &p
  = ∀ x → b x → ∃ l ꞉ aΣv &p , (l val) x


 &PSet-reducible→ : &PSet 𝓥 𝓦 → &PSet 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
 &PSet-reducible→ a b = Σ l ꞉ mΣv a , msg-reducible-g (l val) b

 ∥&PSet-reducible→∥ : &PSet 𝓥 𝓦 → &PSet 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
 ∥&PSet-reducible→∥ a b = Σ l ꞉ mΣv a , ∥msg-reducible-g∥ (l val) b

 &PSet-reducible : &PSet 𝓥 𝓦 → &PSet 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
 &PSet-reducible a b = &PSet-reducible→ a b + &PSet-reducible→ b a

 ∥&PSet-reducible∥ : &PSet 𝓥 𝓦 → &PSet 𝓥' 𝓦' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓥' ⁺ ⊔ 𝓦' ̇
 ∥&PSet-reducible∥ a b = ∥&PSet-reducible→∥ a b + ∥&PSet-reducible→∥ b a


 ESet-reducible-fiber : &PSet 𝓥 𝓦 → ESet 𝓥' 𝓦' 𝓣' → _
 ESet-reducible-fiber &pa pb = ∀ &pb → pb &pb → &PSet-reducible &pa &pb

 ∥ESet-reducible-fiber∥ : &PSet 𝓥 𝓦 → ESet 𝓥' 𝓦' 𝓣' → _
 ∥ESet-reducible-fiber∥ &pa pb = ∀ &pb → pb &pb → ∥&PSet-reducible∥ &pa &pb
 
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
 PSet-ctx-reducible-fiber (&pa , &ic) ctx = ESet-reducible-fiber &pa ctx + &PSet-reducible→ &ic &ic 

 ∥PSet-ctx-reducible-fiber∥ : (&PSet 𝓥 𝓦) × (&PSet 𝓥 𝓦) → ESet 𝓥' 𝓦' 𝓣' → _
 ∥PSet-ctx-reducible-fiber∥ (&pa , &ic) ctx = ∥ESet-reducible-fiber∥ &pa ctx + &PSet-reducible→ &ic &ic

 PSet-ctx-reducible :  PSet 𝓥 𝓦 𝓣 → ESet 𝓥' 𝓦' 𝓣' → _ ̇
 PSet-ctx-reducible pa ctx = ∀ &pa &ic → pa (&pa , &ic) → PSet-ctx-reducible-fiber (&pa , &ic) ctx

 ∥PSet-ctx-reducible∥ :  PSet 𝓥 𝓦 𝓣 → ESet 𝓥' 𝓦' 𝓣' → _ ̇
 ∥PSet-ctx-reducible∥ pa ctx = ∀ &pa &ic → pa (&pa , &ic) → ∥ ∥PSet-ctx-reducible-fiber∥ (&pa , &ic) ctx ∥

 _toCtx : PSet 𝓥 𝓦 𝓣 → ESet 𝓥 𝓦 _
 (pa toCtx) o = Σ λ &ps → pa (o , &ps)


 _toInt : PSet 𝓥 𝓦 𝓣 → ESet 𝓥 𝓦 _
 (pa toInt) o = Σ λ &ps → pa (&ps , o)

 PSet-PSet-reducible-fiber : (&PSet 𝓥 𝓦 × &PSet 𝓥 𝓦) → (&PSet 𝓥' 𝓦' × &PSet 𝓥' 𝓦')
                             → _
 PSet-PSet-reducible-fiber &a@(&pa , &ica) &b@(&pb , &icb)
  = &PSet-reducible &pa &pb + &PSet-reducible &ica &ica + &PSet-reducible &icb &icb

 PSet-PSet-reducible : PSet 𝓥 𝓦 𝓣 → PSet 𝓥' 𝓦' 𝓣' → _
 PSet-PSet-reducible pa pb = ∀ &pa &ica → pa (&pa , &ica) → ∀ &pb &icb → pb (&pb , &icb) → PSet-PSet-reducible-fiber (&pa , &ica) (&pb , &icb)


 _⊑_ : PSet 𝓥 𝓦 𝓣 → PSet 𝓥' 𝓦' 𝓣' → 𝓤ω 
 pa ⊑ pb = ∀{𝓥' 𝓦' 𝓣'} → (ctx : ESet 𝓥' 𝓦' 𝓣') → ∥PSet-ctx-reducible∥ pb ctx → ∥PSet-ctx-reducible∥ pa ctx

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
 Fun' {𝓥 = 𝓥} {𝓦 = 𝓦} p = (q : Σ t ꞉ _ , p t × (¬ &PSet-reducible→ (t .pr₂) (t .pr₂))) → Σ bs ꞉ _ , q .pr₁ .pr₁ (bs ᶜ)

 F⇒&P' : {p : PSet 𝓥 𝓦 𝓣} → Fun' p
        → &PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣)
 F⇒&P' {p = p} f o = Σ q ꞉ _ , f q .pr₁ ＝ o
 
 _ᵀ' : PSet 𝓥 𝓦 𝓣 → ESet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺⁺ ⊔ 𝓣 ⁺)
 (p ᵀ') o = Σ q ꞉ Fun' p , F⇒&P' q ＝ o

 module _ (LEM : ∀{𝓕} → (A : 𝓕 ̇ ) → A + ¬ A) where
  ∄⇒∀ : ∀{𝓤 𝓥} → {A : 𝓤 ̇ } → {B : A → 𝓥 ̇ } →
        ¬ (Σ λ a → B a) →
        ∀ a → ¬ (B a)
  ∄⇒∀ ¬∃ a b = ¬∃ (a , b)

  ¬¬A⇒A : ∀{𝓤} → {A : 𝓤 ̇ } → ¬ (¬ A) → A
  ¬¬A⇒A {_} {A} ¬¬p =
   case LEM A of λ
     { (inl p) → p
     ; (inr ¬p) → 𝟘-elim (¬¬p ¬p)
     }

  ∀⇒∄ : ∀{𝓤 𝓥} → {A : 𝓤 ̇ } → {B : A → 𝓥 ̇ } →
                ¬ (∀ a → B a)
                → (Σ λ a → ¬ (B a))
  ∀⇒∄ {B = B} ∀¬ =
   case LEM (Σ λ a → ¬ (B a))
   of λ { (inl x) → x
        ; (inr x) → 𝟘-elim (∀¬ λ a → ¬¬A⇒A (∄⇒∀ x a) )}


  lemma : ∀{𝓥'' 𝓦'' 𝓣''} → (a : PSet 𝓥 𝓦 𝓣) → (b : PSet 𝓥' 𝓦' 𝓣') → (ctx : ESet 𝓥'' 𝓦'' 𝓣'')
          → (&pa : _) → (&ia : _) → (pi∈a : a (&pa , &ia))
          → (abt-fiber : ESet-reducible-fiber &pa (b ᵀ'))
          → (&pc : _) → (&pc∈ctx : ctx &pc) → (bc-red : PSet-ctx-reducible b ctx)
          → &PSet-reducible &pa &pc
  lemma {𝓥 = 𝓥} {𝓦 = 𝓦} {𝓥' = 𝓥'} {𝓦' = 𝓦'} {𝓥'' = 𝓥''} {𝓦'' = 𝓦''} a b ctx &pa &ia pi∈a abt-fiber &pc &pc∈ctx bc-red
   = case (LEM (&PSet-reducible &pa &pc))
     of λ { (inl x) → x
          ; (inr x) → 𝟘-elim (l3 x)} where
      l1 : ¬ &PSet-reducible &pa &pc → (&pb &ib : &PSet _ _) → (&b∈b : b (&pb , &ib))
      -- Instead of the equality, just use x
           → ∀ x → bc-red &pb &ib &b∈b ＝ inl x → Σ bs ꞉ _ , ((&pb (₀ , bs) × msg-reducible-g bs &pc) + &pb (₁ , bs) × ¬ (msg-reducible-g bs &pa))
      l1 ¬acr &pb &ib &b∈b bc-fiber c
       = case (bc-fiber &pc &pc∈ctx) of
         λ { (inl x) → (x .pr₁ .pr₁) , (inl ((x .pr₁ .pr₂) , (x .pr₂)))
           ; (inr c→b) →
           -- use Σ here so as to avoid ∀⇒∄
             case (LEM ((l : aΣv &pb) → msg-reducible-g (l val) &pa))
             of λ { (inl b→a) → 𝟘-elim (¬acr (inr ((c→b .pr₁) , (λ x bsc → b→a (c→b .pr₂ x bsc .pr₁) x (c→b .pr₂ x bsc .pr₂)))))
                  ; (inr ¬b→a) → let q = ∀⇒∄ ¬b→a in q .pr₁ .pr₁ , inr (q .pr₁ .pr₂ , q .pr₂)} }
      lh : 𝟚 × ×BSet 𝓥' → _
      lh (₀ , bs) = ¬ (msg-reducible-g bs &pa) × 𝟙 {𝓤 ⊔ 𝓥' ⊔ (𝓥'' ⁺) ⊔ 𝓦''}
      lh (₁ , bs) = (msg-reducible-g bs &pc) × 𝟙 {𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦 ⊔ 𝓥'}
      l2 : ¬ &PSet-reducible &pa &pc → (q : Σ t ꞉ _ , b t × (¬ &PSet-reducible→ (t .pr₂) (t .pr₂))) →  Σ res ꞉ (Σ bs ꞉ _ , q .pr₁ .pr₁ (bs ᶜ))
        , lh (res .pr₁)
      l2 ¬acr ((&pb , &ib) , (&b∈b , ¬sred))
       = case (w .pr₂) of
         λ { (inl x) → ((₁ , w .pr₁) , x .pr₁) , x .pr₂ , _ ; (inr x) → ((₀ , w .pr₁) , x .pr₁) , x .pr₂ , _ } where
       q : ∀ {y} → bc-red &pb &ib &b∈b ＝ y → Σ λ x → y ＝ inl x
       q {inl x} eq = x , refl
       q {inr x} eq = 𝟘-elim (¬sred x)
       w = l1 ¬acr &pb &ib &b∈b (q refl .pr₁) (q refl .pr₂)
      l3 : ¬ &PSet-reducible &pa &pc → 𝟘
      l3 ¬acr = case (abt-fiber (F⇒&P' (λ x → l2 ¬acr x .pr₁)) ((λ x → l2 ¬acr x .pr₁) , refl)) of
       λ { (inl a→bt) → ¬acr (inl (a→bt .pr₁ , λ m bsa → let &pbg = a→bt .pr₂ m bsa
                                                             &bsᶜ = &pbg .pr₁ .pr₁
                                                             &∈pb = &pbg .pr₁ .pr₂
                                                             &pb+  = &pbg .pr₁ .pr₂ .pr₁
                                                             &eq  = &pbg .pr₁ .pr₂ .pr₂
                                                             c = l2 ¬acr &pb+ .pr₂
                                                             cc = l11 m &eq c (&pbg .pr₂)
                                                         in cc))
         ; (inr ((bsᶜ , (&pb , w)) , c)) → l12 w (l2 ¬acr &pb .pr₂) c} where
         l11 : ∀{t w} → ∀ m → w ＝ (₁ , t) → lh w
               → t m → _
         l11 m refl c r = c .pr₁ m r
         l12 : ∀{t w} → w ＝ (₀ , t) → lh w → msg-reducible-g t &pa → 𝟘
         l12 refl neq eq = neq .pr₁ eq



  lemma2 : ∀{𝓥'' 𝓦'' 𝓣''} → (a : PSet 𝓥 𝓦 𝓣) → (b : PSet 𝓥' 𝓦' 𝓣') → (ctx : ESet 𝓥'' 𝓦'' 𝓣'')
          → (&pa : _) → (&ia : _) → (pi∈a : a (&pa , &ia))
          → (abt-fiber : ∥ESet-reducible-fiber∥ &pa (b ᵀ'))
          → (&pc : _) → (&pc∈ctx : ctx &pc) → (bc-red : ∥PSet-ctx-reducible∥ b ctx)
          → ∥ ∥PSet-ctx-reducible-fiber∥ (&pa , &ia) ctx ∥
  lemma2 {𝓥 = 𝓥} {𝓦 = 𝓦} {𝓥' = 𝓥'} {𝓦' = 𝓦'} {𝓥'' = 𝓥''} {𝓦'' = 𝓦''} a b ctx &pa &ia pi∈a abt-fiber &pc &pc∈ctx bc-red
   =  case (LEM (∥ ∥PSet-ctx-reducible-fiber∥ (&pa , &ia) ctx ∥))
      of λ { (inl x) → x
           ; (inr x) → 𝟘-elim {!!}} where
      l1 : ¬ ∥ ∥PSet-ctx-reducible-fiber∥ (&pa , &ia) ctx ∥ → (&pb &ib : &PSet _ _) → (&b∈b : b (&pb , &ib))
           → ∥ESet-reducible-fiber∥ &pb ctx → Σ bs ꞉ _ , ((&pb (₀ , bs) × ∥msg-reducible-g∥ bs &pc) + &pb (₁ , bs) × ¬ (∥msg-reducible-g∥ bs &pa))
      l1 ¬acr &pb &ib &b∈b bc-fiber
       = case (bc-fiber &pc &pc∈ctx) of
         λ { (inl x) → (x .pr₁ .pr₁) , (inl ((x .pr₁ .pr₂) , (x .pr₂)))
           ; (inr c→b) →
           -- we need information about the specific aΣv
           -- the only way to do it is to have a finite covering.
           -- TODO fix this.
              case (LEM (Σ l ꞉ aΣv &pb , ¬ ∥msg-reducible-g∥ (l val) &pa)) of
              λ { (inl ¬b→a) → ¬b→a .pr₁ .pr₁ , inr (¬b→a .pr₁ .pr₂ , ¬b→a .pr₂)
                ; (inr b→a) → 𝟘-elim (¬acr ∣ inl (λ &pb₁ x → {!!}) ∣)}}




  theorem : (a : PSet 𝓥 𝓦 𝓣) → (b : PSet 𝓥' 𝓦' 𝓣') → ∥PSet-ctx-reducible∥ a (b ᵀ') → a ⊑ b
  theorem a b abt-red ctx bc-red &pa &ia pi∈a
   = ∥∥-rec ∥∥-is-prop (λ { (inr r) → ∣ inr r ∣
                         ; (inl abt-fib) → {!!} }) (abt-red &pa &ia pi∈a) where
    l2 : _ → ∀ &pc → ctx &pc → _
    l2 abt-fib &pc &pc∈ctx = lemma2 a b ctx &pa &ia pi∈a abt-fib &pc &pc∈ctx bc-red

