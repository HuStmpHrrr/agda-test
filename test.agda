module test where

open import Data.List renaming (map to lmap)
open import Function
open import Data.Empty
open import Data.Unit
open import Level
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality

module _ where
  open import Data.Nat

  data Tree : Set where
    node : List Tree → Tree

  size : Tree → ℕ
  size (node []) = 1
  size (node (x ∷ x₁)) = 1 + size x + (size (node x₁))


module _ {a} {A : Set a} where
  not-empty : List A → Set
  not-empty [] = ⊥
  not-empty (x ∷ l) = ⊤

  infix 4 _`in`_
  data _`in`_ (e : A) : List A → Set a where
    skip : ∀ {l} h → e `in` l → e `in` h ∷ l
    found : ∀ l → e `in` e ∷ l

  `in`-dec : ∀ {h : A} {e l} → e `in` h ∷ l → h ≡ e ⊎ e `in` l
  `in`-dec (skip h ev) = inj₂ ev
  `in`-dec (found l) = inj₁ refl

  `in`⇒not-empty : ∀ {e l} → e `in` l → not-empty l
  `in`⇒not-empty (skip h ev) = tt
  `in`⇒not-empty (found l) = tt

  `in`-relaxation : ∀ {e l} l1 l2 → e `in` l → e `in` l1 ++ l ++ l2
  `in`-relaxation [] l2 (skip h ev) = skip h $ `in`-relaxation [] l2 ev
  `in`-relaxation [] l2 (found l) = found $ l ++ l2
  `in`-relaxation (x ∷ l1) l2 ev = skip x $ `in`-relaxation l1 l2 ev

module _ {a b} {A : Set a} {B : A → Set b} {k : A} {v : B k} where
  ab : Level
  ab = a ⊔ b

  AssocList : Set ab
  AssocList = List (Σ A B)

  _↦_ : ∀ {l : AssocList} → (k , v) `in` l → B k → AssocList
  skip h ev ↦ nv = h ∷ ev ↦ nv
  found l ↦ nv = (k , nv) ∷ l

  ↦-consistent : ∀ {l : AssocList} → (ev : (k , v) `in` l) → (nv : B k) → (k , nv) `in` ev ↦ nv
  ↦-consistent (skip h ev) nv = skip h $ ↦-consistent ev nv
  ↦-consistent (found l) nv = found l

  ↦-safe : ∀ {l : AssocList} {k' v'} → (ev : (k , v) `in` l) → (nv : B k) →
    (ev' : (k' , v') `in` l) → k ≢ k' → (k' , v') `in` ev ↦ nv
  ↦-safe (skip .h ev) nv (skip h ev') neq = skip h $ ↦-safe ev nv ev' neq
  ↦-safe (found l) nv (skip .(_ , _) ev') neq = skip (k , nv) ev'
  ↦-safe (skip .(_ , _) ev) nv (found l) neq = found $ ev ↦ nv
  ↦-safe (found .l) nv (found l) neq with neq refl
  ↦-safe (found .l) nv (found l) neq | ()
