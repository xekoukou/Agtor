{-# OPTIONS --sized-types --cubical #-}

module Abstraction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Function
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Data.Sigma
import Cubical.Data.List as L
open import Cubical.Data.Nat hiding (_·_ ; _+_)
open import Cubical.HITs.SetQuotients
import Cubical.HITs.PropositionalTruncation as Tr
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets

open import Common
open import Projection 
open import SemiRing
open import ProductCommMonoid
open import MTree
import MBree
open import Definitions



