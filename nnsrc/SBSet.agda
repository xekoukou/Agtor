{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Base

open import Lists

module SBSet2 (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇ ) (s-is-set : is-set Secret) (dc : (ascrs scrs : List Secret) → is-decidable (scrs ⊃ ascrs × ascrs ⊃ scrs)) (dc∈ : ∀ x → (ascrs : List (List Secret)) → is-decidable (Σ y ꞉ _ , (x ⊃ y × y ⊃ x) × (y ∈ ascrs))) where

open PropositionalTruncation pt
open import BSet {𝓤} fe pt Msg

S×Msg : 𝓤 ̇
S×Msg = List Secret × (Msg + Secret)

   
data ×BSet : 𝓤 ⁺ ̇  where
 isMsg : BSet → ×BSet
 isSecret : ×BSet
 hasSecret : List Secret → ×BSet

notSame' : {A : 𝓤 ̇} → ∀ lls → 𝓤 ̇
notSame' {A} lls = ((ascrs scrs : List A) → (a : ascrs ∈ lls) → (b : scrs ∈ lls) → (scrs ⊃ ascrs × ascrs ⊃ scrs) → Σ eq ꞉ ascrs ＝ scrs , transport (_∈ lls) eq a ＝ b)

S×BSet' : 𝓤 ⁺ ̇
S×BSet' = List ((List Secret) × ×BSet)


notSame : (lls : S×BSet') → 𝓤 ̇
notSame lls = notSame' (map pr₁ lls)

S×BSet : 𝓤 ⁺ ̇
S×BSet = Σ notSame


lemma : ∀ xs ×bs → (xxs : List ((List Secret) × ×BSet)) → (we : notSame ((xs , ×bs) ∷ xxs)) → notSame xxs
lemma xs ×bs xxs we ascrs scrs a b x with we ascrs scrs (there a) (there b) x
... | refl , refl = refl , refl


lS→×BSet : (lls : List ((List Secret) × ×BSet)) → notSame lls → (List Secret) → 𝟙 {𝓤} + ×BSet 
lS→×BSet [] _ ls = inl _
lS→×BSet ((xs , ×bs) ∷ xxs) we ls
 = case_of_ {B = λ _ → 𝟙 {𝓤} + ×BSet} (dc xs ls)
   λ { (inl _) → inr ×bs
     ; (inr _) → lS→×BSet xxs (lemma xs ×bs xxs we) ls}


⟨_⟩× : S×BSet → S×Msg → 𝓤 ̇
⟨ lls , ns ⟩× (ls , inl msg)
  = case (lS→×BSet lls ns ls) of
     λ { (inl _) → 𝟘
       ; (inr (isMsg bs)) → ⟨ bs ⟩ msg
       ; (inr isSecret) → 𝟘
       ; (inr (hasSecret _)) → 𝟘}
⟨ lls , ns ⟩× (ls , inr xscr)
  = case (lS→×BSet lls ns ls) of
     λ { (inl _) → 𝟘
       ; (inr (isMsg bs)) → 𝟘
       ; (inr isSecret) → 𝟙
       ; (inr (hasSecret tscr)) → foldr (λ x y → y × (xscr ＝ x)) 𝟙 tscr}

-- The property holds for all messages.
×⊨ : S×BSet → 𝓤 ̇
×⊨ P = ∀ a → ⟨ P ⟩× a 

×⊥B : S×BSet
×⊥B = [] , λ { ascrs scrs () b x}


_×&&_ : ×BSet → ×BSet → 𝟙 {𝓤} + ×BSet
isMsg bsa ×&& isMsg bsb = inr (isMsg (bsa && bsb))
isMsg x ×&& isSecret = inl _
isMsg x ×&& hasSecret x₁ = inl _
isSecret ×&& isMsg x = inl _
isSecret ×&& isSecret = inr isSecret
isSecret ×&& hasSecret x = inr (hasSecret x)
hasSecret x ×&& isMsg _ = inl _
hasSecret x ×&& isSecret = inr (hasSecret x)
hasSecret x ×&& hasSecret x₁ = inr (hasSecret (x ++ x₁))


S×&&'' : ∀ als abs → (as : S×BSet') → (nsa : notSame ((als , abs) ∷ as)) → (lb : S×BSet') → (nsb : notSame lb) → Σ m ꞉ List (Σ ls ꞉ (List Secret × ×BSet) , (pr₁ ls) ∈ map pr₁ ((als , abs) ∷ as)) , notSame (map pr₁ m) 
S×&&'' als abs [] nsa bs nsb
 = case (lS→×BSet bs nsb als) of
    λ { (inl x) → [] , (λ {ascrs scrs () b x₁})
      ; (inr bbs) → case (abs ×&& bbs) of
                     λ { (inl x) → [] , (λ {ascrs scrs () b x₁})
                       ; (inr b&abs) → ((als , b&abs) , here refl ∷ []) , λ { ascrs scrs (here refl) (here refl) x → refl , refl }}}
S×&&'' als abs as@((als2 , abs2) ∷ as2) nsa bs nsb
 = case (lS→×BSet bs nsb als) of
    λ { (inl x) → nind
      ; (inr bbs) → case (abs ×&& bbs) of
                     λ { (inl x) → nind
                       ; (inr b&abs) → ((als , b&abs) , here refl ∷ pr₁ nind) , q b&abs}}  where
      ind = S×&&'' als2 abs2 as2 (lemma als abs as nsa) bs nsb
      v : (z : List
           (Sigma (List Secret × ×BSet)
            (λ ls → pr₁ ls ∈ (als2 ∷ map (λ r → pr₁ r) as2)))) → map pr₁ (map (λ (l , c) → l , there c) z) ＝ map pr₁ z
      v [] = refl
      v (x ∷ z) = ap (pr₁ x ∷_) (v z)
      nind = map (λ (l , c) → l , there c) (pr₁ ind) , transport notSame ((v (pr₁ ind)) ⁻¹) (pr₂ ind) 
      q : ∀ b&abs → notSame (als , b&abs ∷ map (λ r → pr₁ r) (pr₁ nind))
      q b&abs ascrs .ascrs (here refl) (here refl) x = refl , refl
      q b&abs ascrs scrs (here refl) (there b) x = {!ii!} where
      
       d : ∀ nind → (b : scrs ∈ map (λ r → pr₁ r) (map (λ r → pr₁ r) nind)) → scrs ∈ map (λ r → pr₁ r) (ascrs , abs ∷ als2 , abs2 ∷ as2)
       d ((pr₃ , pr₄) , ee ∷ aa) (here refl) = {!ee!}
       d ((pr₃ , pr₄) , ee ∷ aa) (there b) = d aa b
       
       ii = nsa als scrs (here refl) (d (pr₁ nind) b) x
      q b&abs ascrs scrs (there a) (here eq) x = {!!}
      q b&abs ascrs scrs (there a) (there b) x = {!!}

S×&&' : (la : S×BSet') → (nsa : notSame la) → (lb : S×BSet') → (nsb : notSame lb) → S×BSet
S×&&' [] nsa _ _ = ×⊥B
S×&&' ((als , abs) ∷ as) wa bs wb
 = case (lS→×BSet bs wb als) of
    λ { (inl x) → ind
      ; (inr x) → let (z , nsz) = ind in {!!}} where
      ind = S×&&' as (lemma als abs as wa) bs wb

_S×&&_ : S×BSet → S×BSet → S×BSet
(la , nsa) S×&& (lb , nsb) = S×&&' la nsa lb nsb


-- ⟨ a && b ⟩ mp = ⟨ a ⟩ mp × ⟨ b ⟩  mp
-- ((a && b) .-is-prop) mp = Σ-is-prop ((a .-is-prop) mp) (λ _ → ((b .-is-prop) mp))
-- -- (a && b) .-is-decidable mp with a .-is-decidable mp | b .-is-decidable mp
-- -- ... | inr x | q = inr λ (w , e) → x w
-- -- ... | inl x | inl y = inl (x , y)
-- -- ... | inl x | inr y = inr λ (w , e) → y e

-- -- _≡ᵇ_ : BSet → BSet → 𝓤 ̇
-- -- A ≡ᵇ B = ⊨ ((A ⟶ B) && (B ⟶ A))

-- -- ¬ᵇ : BSet → BSet
-- -- ⟨ ¬ᵇ A ⟩ mp = ¬ (⟨ A ⟩ mp)
-- -- -is-prop (¬ᵇ A) mp = Π-is-prop fe λ _ → 𝟘-is-prop
-- -- -- -is-decidable (¬ᵇ A) mp with -is-decidable A mp
-- -- -- ... | inl x = inr (λ ¬f → ¬f x)
-- -- -- ... | inr x = inl x

-- -- -- I do not like this definition, because we need to prove the negation
-- -- --  update : But since we have decidability anyway, this is provable immediately
-- -- _─_ : BSet → BSet → BSet
-- -- (a ─ b) = a && (¬ᵇ b)

-- -- _|x|_ : BSet → BSet → BSet
-- -- ⟨ a |x| b ⟩ mp = ⟨ ¬ᵇ (a && b) ⟩ mp × (⟨ a ⟩ mp + ⟨ b ⟩ mp)
-- -- -is-prop (a |x| b) mp
-- --  = Σ-is-prop
-- --     (¬ᵇ (a && b) .-is-prop mp)
-- --     (λ ¬pa&b → +-is-prop (a .-is-prop mp)
-- --     (b .-is-prop mp)
-- --     λ pa pb → ¬pa&b (pa , pb))
-- -- -- -is-decidable (a |x| b) mp with a .-is-decidable mp | b .-is-decidable mp
-- -- -- ... | inl x | inl y = inr (λ (z , _) → z (x , y))
-- -- -- ... | inl x | inr y = inl ((λ (_ , e) → y e) , inl x)
-- -- -- ... | inr x | inl y = inl ((λ (e , _) → x e) , inr y)
-- -- -- ... | inr x | inr y = inr λ { (_ , inl z) → x z ; (_ , inr z) → y z}

-- -- -- I use this definition because of the proof of is-prop
-- -- _||'_ : BSet → BSet → BSet
-- -- a ||' b = (a && b) |x| (a |x| b)


-- -- _||_ : BSet → BSet → BSet
-- -- ⟨ a || b ⟩ mp = ⟨ a && b ⟩ mp + ⟨ ¬ᵇ (a && b) ⟩ mp × (⟨ a ⟩ mp + ⟨ b ⟩ mp)
-- -- -is-prop (a || b) mp (inl x) (inl y) = ap inl ((a && b) .-is-prop mp x y)
-- -- -is-prop (a || b) mp (inl x) (inr y) = 𝟘-elim (pr₁ y x)
-- -- -is-prop (a || b) mp (inr x) (inl y) = 𝟘-elim (pr₁ x y)
-- -- -is-prop (a || b) mp (inr x) (inr y) = ap inr ((a |x| b) .-is-prop mp x y)


-- -- Varᵇ : 𝓤 ⁺ ̇
-- -- Varᵇ = Σ D ꞉ 𝓤 ̇  , (D → BSet)

-- -- Var→BSet : Varᵇ → BSet
-- -- ⟨ Var→BSet (D , f) ⟩ mp = ∥ (Σ x ꞉ D , ⟨ f x ⟩ mp) ∥
-- -- -is-prop (Var→BSet (d , f)) _ = ∥∥-is-prop

-- -- Varᵇ→Set : Varᵇ → Msg → 𝓤 ̇
-- -- Varᵇ→Set (D , f) mp = (Σ x ꞉ D , ⟨ f x ⟩ mp)


-- -- DVarᵇ : 𝓤 ⁺ ̇
-- -- DVarᵇ = Σ D ꞉ 𝓤 ̇  , (D → BSet × BSet)

-- -- -- Redundant
-- -- DVar→×BSet : DVarᵇ → BSet × BSet
-- -- DVar→×BSet (D , f) = Var→BSet (D , pr₁ ∘ f) , Var→BSet (D , pr₂ ∘ f)

-- -- DVarᵇ→Set : DVarᵇ → Msg → 𝓤 ̇
-- -- DVarᵇ→Set (D , f) mp = Varᵇ→Set (D , pr₁ ∘ f) mp × Varᵇ→Set (D , pr₂ ∘ f) mp
