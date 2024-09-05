{-# OPTIONS --without-K --exact-split #-}

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
open import Maybe

module SType-Coalgebra-with-Secrets (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) (s-is-set : is-set Secret) (dec : (a b : Secret) → is-decidable (a ＝ b)) where

open list-decidable dec

open PropositionalTruncation pt
open import UF.ImageAndSurjection pt

open import xBSet fe pt Msg Secret s-is-set dec
open import &PSet (𝟚 × ×BSet) pt
open import PSet pt (&PSet × &PSet) (λ (a1 , a2) (b1 , b2) → (a1 &-&ᵖ b1) , ((a2 &-&ᵖ b2)))
open import Scope fe pt UA Msg Secret s-is-set dec

-- non-empty variance
ExCG : 𝓤 ⁺⁺ ⁺ ̇  → 𝓤 ⁺⁺ ⁺ ̇
ExCG X = Σ D ꞉ 𝓤 ̇  , (D → X)

ExC : 𝓤 ⁺⁺ ⁺ ̇  → 𝓤 ⁺⁺ ⁺ ̇
ExC X = ( Σ B ꞉ ×BSet × ×BSet , (∀ x → ⟨ B .pr₁ .pr₁ ⟩' x + ⟨ B .pr₂ .pr₁ ⟩' x → X))

ExC→G : ∀ X → ExC X → ExCG X
ExC→G X (a , b) = (Σ x ꞉ S×Msg , ⟨ (pr₁ ∘ pr₁) a ⟩' x + ⟨ (pr₁ ∘ pr₂) a ⟩' x) , λ (x , p) → b x p

-- We define the coalgebra of a functor F

-- This is a functor
F : 𝓤 ⁺⁺ ⁺ ̇  → 𝓤 ⁺⁺ ⁺ ̇
F X = PSet × X × ExC X

-- TODO We need to split the structure to internal reducible structure and externally reducible one.

Fm : ∀{X Y} → (f : X → Y) → F X → F Y
Fm f (p , x , (bset , g)) = p , f x , (bset , (λ x bs → f (g x bs)))

Fm-comp :  ∀{X Y Z : 𝓤 ⁺⁺ ⁺ ̇} → (f : X → Y) → (g : Z → X) → ∀ x → (Fm f) (Fm g x) ＝ Fm (f ∘ g) x
Fm-comp f g x = refl

Fm-id : ∀{X : 𝓤 ⁺⁺ ⁺ ̇} → Fm id ∼ id {X = F X}
Fm-id x = refl

-- CoAlgebra

record CoAlgebra : 𝓤 ⁺⁺ ⁺⁺ ̇  where
 field
  E : 𝓤 ⁺⁺ ⁺ ̇
  f : E → F E


module CoAlgebra-morphism (b a : CoAlgebra) where
 private
  module A = CoAlgebra a
  module B = CoAlgebra b

 record coalg-morphism (f : A.E → B.E) : 𝓤 ⁺⁺ ⁺ ̇  where
  constructor co-morph 
  field
   di-comm : Fm f ∘ A.f ＝ B.f ∘ f

 open coalg-morphism public
 
-- Final Coalgebra universal property

module Final-CoAlgebra-universal (final-co : CoAlgebra) where
 open CoAlgebra
 open CoAlgebra-morphism final-co

 uniT : 𝓤 ⁺⁺ ⁺⁺ ̇
 uniT = ∀ a → Σ mo ꞉ Σ (coalg-morphism a) , ((b : Σ (coalg-morphism a)) → pr₁ mo ＝ pr₁ b) 

record Final-CoAlgebra : 𝓤 ⁺⁺ ⁺⁺ ̇  where
 field
  co : CoAlgebra
 open CoAlgebra co public
 open Final-CoAlgebra-universal co public
 field
  uni : uniT

-- According to theorem 2.1 
-- https://ncatlab.org/nlab/show/terminal+coalgebra+for+an+endofunctor
-- F X is is isomorphic to X if X is a final coalgebra
-- TODO Check that this category is univalent and thus isomorphism leads to equalityz
-- The way we defined it , it is univalent, we are in the category of Sets and
-- we have the univalence theorem

module co-iso (fc : Final-CoAlgebra) where
 module Q = Final-CoAlgebra fc
 open CoAlgebra
 open CoAlgebra-morphism

 f-co : CoAlgebra
 E f-co = F Q.E
 f f-co = Fm Q.f

 inv-morph : _
 inv-morph = Q.uni f-co

 inv = inv-morph .pr₁ .pr₁

 morph : Σ (coalg-morphism Q.co Q.co)
 pr₁ morph = inv ∘ Q.f
 di-comm (pr₂ morph) =  dfunext fe (λ x → Fm-comp (pr₁ (inv-morph .pr₁)) Q.f (Q.f x)) ⁻¹ ∙ ap (_∘ Q.f) (inv-morph .pr₁ .pr₂ .di-comm) 


 morph-Id : Σ (coalg-morphism Q.co Q.co)
 pr₁ morph-Id = λ x → x
 di-comm (pr₂ morph-Id) with (Fm {X = Q.E} id) | dfunext fe (Fm-id {X = Q.E})
 ... | _ | refl = refl

 inv∘Qf=id : inv ∘ Q.f ＝ (λ x → x)
 inv∘Qf=id = l2 ⁻¹ ∙ l3 where
  l1 = Q.uni Q.co
  C = pr₁ l1
  l2 : pr₁ C ＝ pr₁ morph
  l2 = pr₂ l1 morph

  l3 : pr₁ C ＝ pr₁ morph-Id
  l3 = pr₂ l1 morph-Id

 Qf∘inv=id : Q.f ∘ inv ＝ (λ x → x)
 Qf∘inv=id = inv-morph .pr₁ .pr₂ .di-comm ⁻¹ ∙ (dfunext fe (λ x → Fm-comp (pr₁ (inv-morph .pr₁)) Q.f x) ∙ (ap Fm inv∘Qf=id ∙ dfunext fe Fm-id))

 QE=FQE : Q.E ＝ F Q.E
 QE=FQE = eqtoid (UA _) Q.E (F Q.E) (qinveq Q.f (inv , (λ x → ap (λ f → f x) inv∘Qf=id) , (λ x → ap (λ f → f x) Qf∘inv=id)))

module prod (fc : Final-CoAlgebra) where

 module Q = Final-CoAlgebra fc
 open CoAlgebra
 open CoAlgebra-morphism

 

module embed (fc : Final-CoAlgebra) (_∈?_ : ∀ s ls → is-decidable (s ∈ ls)) where
 open co-iso fc

 open CoAlgebra
 open CoAlgebra-morphism
 open ∈-dec _∈?_
 open PSet-scope _∈?_

-- We need to limit scope when we send msg between the two systems
-- and remove the scope when we send the msg to the outside world
-- This function does the actual limitation

-- lscope does not change the next step, only the current step.
-- thus the next Q.E contains all the necessary information for the composition
-- that we do in the next function.

-- TODO this is no longer necessary. I have implented scope inside the composition
-- function.
-- Also I have distilled the trick here in lim-rec in Scope.agda
 lscope : {A : 𝓤 ⁺⁺ ⁺ ̇} → List Secret → F A → F A
 lscope [] q = q
 lscope {A} (s ∷ ls) (p , x , ((BA , BM) , f))
  = scopePM (s ∷ ls) p , x , ((limitM× s ls BA , limitM× s ls BM) , q s ls) where
    q : ∀ s ls → (x : S×Msg) →
        ⟨ pr₁ (limitM× s ls BA) ⟩' x +
        ⟨ pr₁ (limitM× s ls BM) ⟩' x →
        A
    q s [] mp@(ws , msg) d = l1 (s ∈? ws) d where
     l1 : (w : (s ∈ ws) + (s ∈ ws → 𝟘)) →
      Lim ((BA .pr₁ .pr₁) (ws , msg)) (+→𝟚 w) +
      Lim ((BM .pr₁ .pr₁) (ws , msg)) (+→𝟚 w) → A
     l1 (inl x) (inl ())
     l1 (inl x) (inr ())
     l1 (inr x) d = f mp d

    q s (l ∷ ls) mp@(ws , msg) d = l1 (s ∈? ws) d  where
     l1 : (w : (s ∈ ws) + (s ∈ ws → 𝟘)) →
      limitMPr l ls (Lim (BA .pr₁ .pr₁ (ws , msg)) (+→𝟚 w)) (ws , msg) +
      limitMPr l ls (Lim (BM .pr₁ .pr₁ (ws , msg)) (+→𝟚 w)) (ws , msg) →
      A
     l1 (inl x) d with limitMPr l ls 𝟘 mp | (limitMPr-𝟘 l ls mp)
     l1 (inl x) (inl ()) | r | refl
     l1 (inl x) (inr ()) | r | refl
     l1 (inr x) d = q l ls (ws , msg) d

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
  = (Σ d ꞉ D , (𝟚 + Σ (λ msg → ⟨ (bax d ×&& bmy d) bset ⟩' msg + ⟨ (bay d ×&& bmx d) bset ⟩' msg)))
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
    =   (Σ d ꞉ D , ⟨ (sbax d) bset ⟩' mp + ⟨ (sbay d) bset ⟩' mp)
      , λ { (d , inl px) → scope d , lim-rec' (scope d) (bax d) px (λ z → Q.f (pr₂ (nxcf d) mp (inl z))) , y d
          ; (d , inr py) → scope d , lim-rec' (scope d) (bay d) py (λ z → Q.f (pr₂ (nycf d) mp (inl z))) , (x d)}
  pr₂ e mp@(_ , inl _) (inr w)
    =   (Σ d ꞉ D , ⟨ (sbmx d) bset ⟩' mp + ⟨ (sbmy d) bset ⟩' mp)
      , λ { (d , inl px) → scope d , lim-rec' (scope d) (bmx d) px (λ z → Q.f (pr₂ (nxcf d) mp (inr z))) , (y d)
          ; (d , inr py) → scope d , lim-rec' (scope d) (bmy d) py (λ z → Q.f (pr₂ (nycf d) mp (inr z))) , (x d)}
  pr₂ e mp@(_ , inr scr) (inl v)
    =   (Σ d ꞉ D , ⟨ (sbax d) bset ⟩' mp + ⟨ (sbay d) bset ⟩' mp)
    -- We limit the scope based on the current one, not the next one
      , λ { (d , inl px) → remove scr (scope d) , lim-rec' (scope d) (bax d) px (λ z → Q.f (pr₂ (nxcf d) mp (inl z))) , (y d)
          ; (d , inr py) → remove scr (scope d) , lim-rec' (scope d) (bay d) py (λ z → Q.f (pr₂ (nycf d) mp (inl z))) , (x d)}
  pr₂ e mp@(_ , inr scr) (inr w)
    =   (Σ d ꞉ D , ⟨ (sbmx d) bset ⟩' mp + ⟨ (sbmy d) bset ⟩' mp)
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



