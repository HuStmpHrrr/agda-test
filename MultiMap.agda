{-# OPTIONS --safe #-}

module MultiMap where

open import Data.Nat renaming (ℕ to Nat ; _⊔_ to max)
open import Data.List
open import Data.Empty
open import Data.Unit using (⊤ ; tt)

open import Prelude.Function
open import Prelude.Product

open import Relation.Nullary

open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.PropositionalEquality

open import Data.List.Properties

open import Data.Nat.Properties

-- some list concepts

module _ {a} {A : Set a} where
  not-empty : List A → Set
  not-empty [] = ⊥
  not-empty (_ ∷ _) = ⊤

  not-empty-relax : (l1 l l2 : List A) → not-empty l → not-empty $ l1 ++ l ++ l2
  not-empty-relax [] [] l2 ()
  not-empty-relax [] (x ∷ l) l2 ev = tt
  not-empty-relax (x ∷ l1) l l2 ev = tt

  ++-not-emptyʳ : ∀ {l : List A} → not-empty (l ++ []) → not-empty l
  ++-not-emptyʳ {l = l} rewrite ++-identityʳ l = λ z → z

  infix 4 _∈_
  data _∈_ (e : A) : List A → Set a where
    skip : ∀ {l} h → e ∈ l → e ∈ h ∷ l
    found : ∀ l → e ∈ e ∷ l

  
-- let's start with something easy from natural numbers

data OrderDec (a b : Nat) : Set where
  le : (a≤b : a ≤ b) → OrderDec a b
  gt : (a>b : a > b) → OrderDec a b


dec-≤ : (a b : Nat) → OrderDec a b
dec-≤ a b with a ≤? b
dec-≤ a b | yes p = le p
dec-≤ a b | no ¬p = gt $ ≰⇒> ¬p


--| maximum of an non-empty list
⨆ : Σ (List Nat) not-empty → Nat
⨆ ([] , ())
⨆ (x ∷ [] , tt) = x
⨆ (x ∷ x₁ ∷ l , tt) = max x $ ⨆ (x₁ ∷ l , _)

module _ where
  open ≤-Reasoning
  
  ⨆-upper-bound : ∀ (l : List Nat) → (ev : not-empty l) → (e : Nat) → e ∈ l → e ≤ ⨆ (l , ev)
  ⨆-upper-bound [] ev e ()
  ⨆-upper-bound (x ∷ []) ev e (skip .x ())
  ⨆-upper-bound (x ∷ []) ev .x (found .[]) = ≤-refl
  ⨆-upper-bound (x ∷ x₁ ∷ l) ev e c with dec-≤ x $ ⨆ (x₁ ∷ l , tt)
  ⨆-upper-bound (x ∷ x₁ ∷ l) ev e c | le a≤b rewrite m≤n⇒m⊔n≡n a≤b with c
  ... | skip .x c' = ⨆-upper-bound (x₁ ∷ l) _ e c'
  ... | found t    = a≤b
  ⨆-upper-bound (x ∷ x₁ ∷ l) ev e c | gt a>b rewrite m≤n⇒n⊔m≡n $ <⇒≤ a>b with c
  ... | skip .x c' = begin
                     e                       ≤⟨ ⨆-upper-bound (x₁ ∷ l) _ e c' ⟩ 
                     ⨆ (x₁ ∷ l , tt)         ≤⟨ ≤-step ≤-refl ⟩
                     (suc $ ⨆ (x₁ ∷ l , tt)) ≤⟨ a>b ⟩
                     x ∎
  ... | found t    = ≤-refl

  ⨆-relaxationʳ : (l l2 : List Nat) → (ev : not-empty l) →
                ⨆ (l , ev) ≤ ⨆ (l ++ l2 , not-empty-relax [] l l2 ev)
  ⨆-relaxationʳ [] l2 ()
  ⨆-relaxationʳ (x ∷ []) l2 tt = ⨆-upper-bound (x ∷ l2) _ x (found l2)
  ⨆-relaxationʳ (x ∷ x₁ ∷ l) l2 tt with dec-≤ x $ ⨆ $ (x₁ ∷ l , tt)
  ⨆-relaxationʳ (x ∷ x₁ ∷ l) l2 tt | le a≤b = begin
    max x ((⨆ (x₁ ∷ l , tt)))     ≡⟨ m≤n⇒m⊔n≡n a≤b ⟩
    ⨆ (x₁ ∷ l , tt)               ≤⟨ ⨆-relaxationʳ (x₁ ∷ l) l2 tt ⟩
    ⨆ (x₁ ∷ l ++ l2 , tt)         ≤⟨ n≤m⊔n x (⨆ (x₁ ∷ l ++ l2 , tt)) ⟩
    max x (⨆ (x₁ ∷ l ++ l2 , tt)) ∎
  ⨆-relaxationʳ (x ∷ x₁ ∷ l) l2 tt | gt a>b = begin
    max x ((⨆ (x₁ ∷ l , tt)))     ≡⟨ m≤n⇒n⊔m≡n $ <⇒≤ a>b ⟩
    x                             ≤⟨ m≤m⊔n x (⨆ (x₁ ∷ l ++ l2 , tt)) ⟩
    max x (⨆ (x₁ ∷ l ++ l2 , tt)) ∎


  ⨆-relaxation : (l1 l l2 : List Nat) → (ev : not-empty l) →
               ⨆ (l , ev) ≤ ⨆ (l1 ++ l ++ l2 , not-empty-relax l1 l l2 ev)
  ⨆-relaxation l1 [] l2 ()
  ⨆-relaxation [] (x ∷ l) l2 tt = ⨆-relaxationʳ (x ∷ l) l2 tt
  ⨆-relaxation (x₁ ∷ []) (x ∷ l) l2 tt = begin
    ⨆ (x ∷ l , tt)                ≤⟨ ⨆-relaxationʳ (x ∷ l) l2 _ ⟩
    ⨆ (x ∷ l ++ l2 , tt)          ≤⟨ n≤m⊔n x₁ (⨆ (x ∷ l ++ l2 , tt)) ⟩
    max x₁ (⨆ (x ∷ l ++ l2 , tt)) ∎
  ⨆-relaxation (x₁ ∷ x₂ ∷ l1) (x ∷ l) l2 tt = 
    begin
      ⨆ (x ∷ l , tt)                           ≤⟨ ⨆-relaxation (x₂ ∷ l1) (x ∷ l) l2 tt ⟩
      ⨆ (x₂ ∷ l1 ++ x ∷ l ++ l2 , tt)          ≤⟨ n≤m⊔n x₁ (⨆ (x₂ ∷ l1 ++ x ∷ l ++ l2 , tt)) ⟩
      max x₁ (⨆ (x₂ ∷ l1 ++ x ∷ l ++ l2 , tt)) ∎


  suc-⨆-fresh : ∀ (l : List Nat) → (ev : not-empty l) → ¬ (suc (⨆ (l , ev)) ∈ l)
  suc-⨆-fresh [] ()
  suc-⨆-fresh (x ∷ []) tt (skip .x ())
  suc-⨆-fresh (x ∷ x₁ ∷ l) tt c with dec-≤ x $ ⨆ (x₁ ∷ l , tt)
  suc-⨆-fresh (x ∷ x₁ ∷ l) tt c | le a≤b rewrite m≤n⇒m⊔n≡n a≤b with c
  ... | skip .x ev' = suc-⨆-fresh (x₁ ∷ l) _ ev'
  ... | found _ = <⇒≱ a≤b ≤-refl
  suc-⨆-fresh (x ∷ x₁ ∷ l) tt c | gt a>b rewrite m≤n⇒n⊔m≡n $ <⇒≤ a>b with c
  ... | skip .x ev' = let contra = ⨆-upper-bound (x₁ ∷ l) tt (suc x) ev'
                          sx<x   : suc x < x
                          sx<x   = begin
                            suc (suc x)           ≤⟨ s≤s contra ⟩
                            suc (⨆ (x₁ ∷ l , tt)) ≤⟨ a>b ⟩
                            x                     ∎
                            in <⇒≱ sx<x $ ≤-step ≤-refl
