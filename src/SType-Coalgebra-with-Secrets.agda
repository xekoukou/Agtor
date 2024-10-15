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

module SType-Coalgebra-with-Secrets (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) (dec : (a b : Secret) → is-decidable (a ＝ b)) where

open list-decidable dec

open PropositionalTruncation pt
open import UF.ImageAndSurjection pt

open import xBSet fe pt Msg Secret
open import &PSet (𝟚 × ×BSet) pt
open import PSet pt (&PSet × &PSet) (λ (a1 , a2) (b1 , b2) → (a1 &-&ᵖ b1) , ((a2 &-&ᵖ b2)))
open import Scope fe pt Msg Secret

open import CoAlgebra fe pt UA Msg Secret dec

module embed (fc : Final-CoAlgebra) (_∈?_ : ∀ s ls → is-decidable (s ∈ ls)) where
 open co-iso fc

 open CoAlgebra
 open CoAlgebra-morphism
 open ∈-dec _∈?_
 open PSet-scope _∈?_

-- This function combines the variance introduced by a function and the parallel composition
-- of two systems. We need to define it this way, because parallel composition
-- introduces this variance when the two systems interact with each other

-- It takes two Q.E and their scope, The two Q.E are not scope limited.
-- It returns a scope limited F ... but the next step is not scope limited.

-- TODO limit scope inside this  function!!!! 
 ExCGP : ExCG (List Secret × F Q.E × F Q.E) → F (ExCG (List Secret × F Q.E × F Q.E))
 -- The PSet
 pr₁ (ExCGP (D , var))
  = Var→PSet λ d → scopePM (scope d) (p d) where
   scope = λ d → var d .pr₁
   a = λ d → var d .pr₂ .pr₁
   b = λ d → var d .pr₂ .pr₂

   -- PSet
   p = λ d → pr₁ (a d) &ᵖ pr₁ (b d)

 pr₁ (pr₂ (ExCGP (D , var)))
 -- The new internal reduction case, it describes the possible internal reduction of the system if possible.

 -- The new Variance
 -- It takes 3 cases
  = (Σ d ꞉ D , (𝟚 + Σ (λ msg → ⟨ (bax d ×&& bmy d) bset ⟩ msg + ⟨ (bay d ×&& bmx d) bset ⟩ msg)))
 -- 1. Internal reduction of system X
    , λ { (d , inl ₀) → scope d , x d , Q.f (iy d)
 -- 2. internal reduction of system Y
        ; (d , inl ₁) → scope d , y d , Q.f (ix d)
 -- 3. communication between X and Y
        ; (d , inr (mp@(ls , inr scr) , (inl (xa , ym)))) → (scr ∷ scope d) , Q.f (pr₂ (nxcf d) mp (inl xa)) , (Q.f (pr₂ (nycf d) mp (inr ym)))
        ; (d , inr (mp@(ls , inr scr) , (inr (ya , xm)))) → (scr ∷ scope d) , (Q.f (pr₂ (nxcf d) mp (inr xm))) , (Q.f (pr₂ (nycf d) mp (inl ya)))
        ; (d , inr (mp@(ls , inl msg) , (inl (xa , ym)))) → scope d , (Q.f (pr₂ (nxcf d) mp (inl xa))) , (Q.f (pr₂ (nycf d) mp (inr ym)))
        ; (d , inr (mp@(ls , inl msg) , (inr (ya , xm)))) → scope d , (Q.f (pr₂ (nxcf d) mp (inr xm))) , (Q.f (pr₂ (nycf d) mp (inl ya)))} where
  scope = λ d → var d .pr₁
  x = λ d → var d .pr₂ .pr₁
  y = λ d → var d .pr₂ .pr₂

  nxcf : D → ExC Q.E
  nxcf d = (pr₂ ∘ pr₂) (x d)
  nycf : D → ExC Q.E
  nycf d = pr₂ (pr₂ (y d))

  bax : D → ×BSet
  bax d = (pr₁ ∘ pr₁) (nxcf d)
  bmx : D → ×BSet
  bmx d = (pr₂ ∘ pr₁) (nxcf d)

  bay : D → ×BSet
  bay d = pr₁ (pr₁ (nycf d))
  bmy : D → ×BSet
  bmy d = pr₂ (pr₁ (nycf d))

  iy : D → Q.E
  iy d = pr₁ (pr₂ (y d))
 
  ix : D → Q.E
  ix d = (pr₁ ∘ pr₂) (x d)

 pr₂ (pr₂ (ExCGP (D , var))) = e where
  scope = λ d → var d .pr₁
  x = λ d → var d .pr₂ .pr₁
  y = λ d → var d .pr₂ .pr₂

  nxcf : D → ExC Q.E
  nxcf d = pr₂ (pr₂ (x d))
  nycf : D → ExC Q.E
  nycf d = pr₂ (pr₂ (y d))

  bax : D → ×BSet
  bax d = pr₁ (pr₁ (nxcf d))
  bmx : D → ×BSet
  bmx d = pr₂ (pr₁ (nxcf d))

  bay : D → ×BSet
  bay d = pr₁ (pr₁ (nycf d))
  bmy : D → ×BSet
  bmy d = pr₂ (pr₁ (nycf d))

  sbax : D → ×BSet
  sbax d = limitM×' (scope d) (bax d)
  sbmx : D → ×BSet
  sbmx d = limitM×' (scope d) (bmx d)

  sbay : D → ×BSet
  sbay d = limitM×' (scope d) (bay d)
  sbmy : D → ×BSet
  sbmy d = limitM×' (scope d) (bmy d)



-- This function expresses the output if a new communication happens.
-- The existence of the communication tells us something about ourselves.
-- Like a box that may contain a cat, opening the box tells us if there is a cat or not.
-- Here is a msg is received , it tells us that there was an actor that could receive the msg.
-- The superposition collapses.


-- The new ×BSets
  ba : ×BSet
  ba = Var→×BSet (D , (λ d → (sbax d) ×|| (sbay d)))

  bm : ×BSet
  bm = Var→×BSet (D , (λ d → (sbmx d) ×|| (sbmy d)))

  e : ExC (ExCG (List Secret × F Q.E × F Q.E))
  pr₁ e = ba , bm
  pr₂ e mp@(_ , inl _) (inl v)
    =   (Σ d ꞉ D , ⟨ (sbax d) bset ⟩ mp + ⟨ (sbay d) bset ⟩ mp)
      , λ { (d , inl px) → scope d , lim-rec' (scope d) (bax d) px (λ z → Q.f (pr₂ (nxcf d) mp (inl z))) , y d
          ; (d , inr py) → scope d , lim-rec' (scope d) (bay d) py (λ z → Q.f (pr₂ (nycf d) mp (inl z))) , (x d)}
  pr₂ e mp@(_ , inl _) (inr w)
    =   (Σ d ꞉ D , ⟨ (sbmx d) bset ⟩ mp + ⟨ (sbmy d) bset ⟩ mp)
      , λ { (d , inl px) → scope d , lim-rec' (scope d) (bmx d) px (λ z → Q.f (pr₂ (nxcf d) mp (inr z))) , (y d)
          ; (d , inr py) → scope d , lim-rec' (scope d) (bmy d) py (λ z → Q.f (pr₂ (nycf d) mp (inr z))) , (x d)}
  pr₂ e mp@(_ , inr scr) (inl v)
    =   (Σ d ꞉ D , ⟨ (sbax d) bset ⟩ mp + ⟨ (sbay d) bset ⟩ mp)
    -- We limit the scope based on the current one, not the next one
      , λ { (d , inl px) → remove scr (scope d) , lim-rec' (scope d) (bax d) px (λ z → Q.f (pr₂ (nxcf d) mp (inl z))) , (y d)
          ; (d , inr py) → remove scr (scope d) , lim-rec' (scope d) (bay d) py (λ z → Q.f (pr₂ (nycf d) mp (inl z))) , (x d)}
  pr₂ e mp@(_ , inr scr) (inr w)
    =   (Σ d ꞉ D , ⟨ (sbmx d) bset ⟩ mp + ⟨ (sbmy d) bset ⟩ mp)
      , λ { (d , inl px) → remove scr (scope d) , lim-rec' (scope d) (bmx d) px (λ z → Q.f (pr₂ (nxcf d) mp (inr z))) , (y d)
          ; (d , inr py) → remove scr (scope d) , lim-rec' (scope d) (bmy d) py (λ z → Q.f (pr₂ (nycf d) mp (inr z))) , (x d)}



 ExCGP-co : CoAlgebra
 E ExCGP-co = ExCG (List Secret × F Q.E × F Q.E)
 f ExCGP-co = ExCGP

 _&ᶠ_ : Q.E → Q.E → Q.E
 a &ᶠ b = Q.uni ExCGP-co .pr₁ .pr₁ (𝟙 , (λ x → [] , Q.f a , Q.f b))




 ∣P' : ExCG (F Q.E) → F (ExCG (F Q.E))
 pr₁ (∣P' (D , f)) = (Var→PSet (pr₁ ∘ f))
 pr₁ (pr₂ (∣P' (D , f))) = D , (Q.f ∘ pr₁ ∘ pr₂ ∘ f)
 pr₂ (pr₂ (∣P' (D , f)))
  = DVar→×BSet (D , (λ d → (pr₁ ∘ pr₂ ∘ pr₂ ∘ f) d))
    , λ { mp (inl _) →   ×Varᵇ→Set (D , (pr₁ ∘ pr₁ ∘ pr₂ ∘ pr₂ ∘ f)) mp
                       , λ { (d , v) → Q.f ((pr₂ ∘ pr₂ ∘ pr₂ ∘ f) d mp (inl v))}
        ; mp (inr _) →   ×Varᵇ→Set (D , (pr₂ ∘ pr₁ ∘ pr₂ ∘ pr₂ ∘ f)) mp
                       , λ { (d , v) → Q.f ((pr₂ ∘ pr₂ ∘ pr₂ ∘ f) d mp (inr v))}} where
    w = λ d → (pr₁ ∘ pr₂ ∘ pr₂ ∘ f) d

 -- --Maybe this is easier to understand.
 -- -- With this definition, one understands that when we receive a msg, we actually also learn something about the prior superposition. The previous definition does not make this clear.
 -- ∣P : (F Q.E + 𝟙 {𝓤}) × F Q.E → F ((F Q.E + 𝟙 {𝓤}) × F Q.E)
 -- ∣P (inl (px , x , (bax , bmx) , fx) , (py , y , (bay , bmy) , fy))
 --   =   (px ∣ᵖ py)
 --     , ((inl (Q.f x)) ,   (Q.f y))
 --     , ((bax || bay) , (bmx || bmy))
 --       , (λ { x (inl (inl (vx , vy))) → inl (Q.f (fx x (inl vx))) , Q.f (fy x (inl vy)) 
 --            ; x (inl (inr (_ , inl vx))) → inr ⋆ , Q.f (fx x (inl vx))
 --            ; x (inl (inr (_ , inr vy))) → inr ⋆ , Q.f (fy x (inl vy))
 --            ; x (inr (inl (vx , vy))) → inl (Q.f (fx x (inr vx))) , Q.f (fy x (inr vy)) 
 --            ; x (inr (inr (_ , inl vx))) → inr ⋆ , Q.f (fx x (inr vx))
 --            ; x (inr (inr (_ , inr vy))) → inr ⋆ , Q.f (fy x (inr vy))
 --            })
 -- ∣P (inr _ , (py , y , (bay , bmy) , fy)) = py , ((inr ⋆) , (Q.f y)) , ((bay , bmy) , (λ x p → (inr ⋆) , (Q.f (fy x p))))


 ∣P'-co : CoAlgebra
 E ∣P'-co = ExCG (F Q.E)
 f ∣P'-co = ∣P'

 _∣ᶠ_ : Q.E → Q.E → Q.E
 a ∣ᶠ b = Q.uni ∣P'-co .pr₁ .pr₁ ((𝟙 {𝓤} + 𝟙 {𝓤}) , (λ { (inl _) → Q.f a ; (inr _) → Q.f b}))



