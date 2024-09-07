{-# OPTIONS --safe --guardedness --without-K --exact-split #-}

open import MLTT.Spartan hiding (𝟚)
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import UF.Base

module SType-Coalgebra-realized (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : _) (Msg : 𝓤 ̇) where

open PropositionalTruncation pt
open import BSet fe pt Msg
open import PSet fe pt Msg
open import SType-Coalgebra fe pt UA Msg


record SType : 𝓤 ⁺⁺ ̇  where
 coinductive
 field
  supPos : PSet
  inner : SType
  extern : ExC SType
  
open SType

record STypeEq (a b : SType) : 𝓤 ⁺⁺ ̇  where
 coinductive
 field
  psEq : supPos a ＝ supPos b
  inEq : STypeEq (inner a) (inner b)
  extEq : Σ ×BsEq ꞉ pr₁ (extern a) ＝ pr₁ (extern b) , (∀ x p → STypeEq (pr₂ (extern a) x p) (pr₂ (extern b) x (transport (λ z → ⟨ pr₁ z ⟩ x + ⟨ pr₂ z ⟩ x) ×BsEq p))) 
  

stEq-refl : ∀{ a} → STypeEq a a
STypeEq.psEq (stEq-refl {a}) = refl
STypeEq.inEq (stEq-refl {a}) = stEq-refl
STypeEq.extEq (stEq-refl {a}) = refl , λ x p → stEq-refl

stEq→eq : ∀{ a b} → STypeEq a b → a ＝ b
stEq→eq x = {!!}


-- TODO SType is a Set ?!?!?

st-CoAlgebra : CoAlgebra
CoAlgebra.E st-CoAlgebra = SType
CoAlgebra.f st-CoAlgebra x = supPos x , (inner x) , (extern x)


inv : PSet × SType × ExC SType → SType
supPos (inv (a , b , c)) = a
inner (inv (a , b , c)) = b
extern (inv (a , b , c)) = c

module _ where
 open CoAlgebra st-CoAlgebra

 inv-f-iso : f ∘ inv ＝ (λ x → x)
 inv-f-iso = dfunext fe (λ x → refl)

 f-inv-iso : inv ∘ f ＝ (λ x → x)
 f-inv-iso = dfunext fe (λ x → stEq→eq (r x)) where
  r : ∀ x → STypeEq _ _
  STypeEq.psEq (r x) = refl
  STypeEq.inEq (r x) = stEq-refl
  STypeEq.extEq (r x) = refl , (λ mp p → stEq-refl)

module _ where

 open CoAlgebra
 open CoAlgebra-morphism st-CoAlgebra


 open Final-CoAlgebra 

 private
  module FC = CoAlgebra st-CoAlgebra
   
 st-FCoAlgebra : Final-CoAlgebra
 co st-FCoAlgebra = st-CoAlgebra
 uni st-FCoAlgebra a = (d ∘ (f a) , co-morph refl) , q  where
  d : F (E a) → SType
  supPos (d (ps , int , ex)) = ps
  inner (d (ps , int , ex)) = d (f a int)
  extern (d (ps , int , (ex1 , ex2))) = ex1 , (λ x x₁ → d (f a (ex2 x x₁))) 

  q : (b : Σ (coalg-morphism a)) →
       (λ x → d (f a x)) ＝ pr₁ b
       
  q (t , eq) = ap (λ z → λ x → z (f a x)) e ∙ ap (inv ∘_) (di-comm eq) ∙ ap (_∘ t) f-inv-iso where
   e : d ＝ inv ∘ Fm t
   e = dfunext fe (λ x → (stEq→eq {a = d x} {b = (inv ∘ Fm t) x}) (s x)) where
    s : (x : F (E a)) → STypeEq (d x) (inv ((Fm t) x))
    STypeEq.psEq (s (p , ix , ex)) = refl
    STypeEq.inEq (s (p , ix , ex)) with (t ix) | ap (λ z → z ix) ((ap (inv ∘_) (di-comm eq) ∙ ap (_∘ t) f-inv-iso))
    ... | _ | refl = s (f a ix)
    pr₁ (STypeEq.extEq (s (p , ix , ex))) = refl
    pr₂ (STypeEq.extEq (s (p , ix , ex))) x v with (t (pr₂ ex x v)) | ap (λ z → z ((pr₂ ex x v))) ((ap (inv ∘_) (di-comm eq) ∙ ap (_∘ t) f-inv-iso))
    ... | _ | refl = s (f a (pr₂ ex x v))

 -- record S : 𝓤 ⁺⁺ ̇  where
 --  coinductive
 --  field
 --   sP : PSet
 --   i : S
 --   e : ExC S
 --   more : 𝟚
   
 -- open S

 -- record SS : 𝓤 ⁺⁺ ̇  where
 --  coinductive
 --  field
 --   sP : PSet
 --   i : SS
 --   e : ExC SS
 --   more : 𝟚
   
 -- open SS



 -- ff : S → F S
 -- ff s = sP s , (i s) , e s

 -- dd : S → SType
 -- supPos (dd s) = pr₁ (ff s)
 -- inner (dd s) = dd (pr₁ (pr₂ (ff s)))
 -- extern (dd s) = (pr₁ (pr₂ (pr₂ (ff s)))) , (λ x p → dd ((pr₂ (pr₂ (pr₂ (ff s)))) x p))

 -- sco : CoAlgebra
 -- E sco = S
 -- f sco = ff

 -- dd-morph : coalg-morphism sco dd
 -- di-comm dd-morph = refl


 -- qq : (b : Σ (coalg-morphism (record { E = S ; f = ff }))) →
 --      (λ x → dd x) ＝ pr₁ b
 -- qq (t , eq) = ee where
 --   ee = dfunext fe λ x → stEq→eq (ss x) where
 --    ss : (x : S) → STypeEq (dd x) (t x)
 --    STypeEq.psEq (ss s) = ap (λ z → pr₁ (z s)) (di-comm eq)
 --    STypeEq.inEq (ss s) with inner (t s) | (ap (λ z → pr₁ (pr₂ (z s))) (di-comm eq))
 --    ... | .(t (i s)) | refl = ss (i s)
 --    -- This does not work because the termination checker does not understand that
 --    -- the trasport is qc
   
 --    -- transport (λ z → STypeEq (dd (i s)) z)
 --    --                        (ap (λ z → pr₁ (pr₂ (z s))) (di-comm eq)) (ss (i s))
 --    pr₁ (STypeEq.extEq (ss s)) with extern (t s) | (ap (λ z → pr₂ (pr₂ (z s))) (di-comm eq))
 --    ... | .(pr₁ (e s) , (λ x bs → t (pr₂ (e s) x bs))) | refl = refl
 --    pr₂ (STypeEq.extEq (ss s)) x p with extern (t s) | (ap (λ z → pr₂ (pr₂ (z s))) (di-comm eq))
 --    ... | .(pr₁ (e s) , (λ x bs → t (pr₂ (e s) x bs))) | refl = ss (pr₂ (e s) x p)
