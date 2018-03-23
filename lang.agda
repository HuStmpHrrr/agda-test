{-# OPTIONS --safe #-}

open import Agda.Builtin.Size
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality

record Lang (i : Size) (A : Set) : Set where
  coinductive
  field
    ν : Bool
    δ : ∀{j : Size< i} → A → Lang j A

open Lang

∅ : ∀ {i A} → Lang i A
ν ∅ = false
δ ∅ _ = ∅

ε : ∀ {i A} → Lang i A
ν ε   = true
δ ε _ = ∅

_+_ : ∀ {i A} → Lang i A → Lang i A → Lang i A
ν (a + b) = ν a ∨ ν b
δ (a + b) x = δ a x + δ b x

infixl 10 _+_

_·_ : ∀ {i A} → Lang i A → Lang i A → Lang i A
ν (a · b)   = ν a ∧ ν b
δ (a · b) x = if ν a then δ a x · b + δ b x else δ a x · b

infixl 20 _·_

_* : ∀ {i A} → Lang i A → Lang i A
ν (a *)   = true
δ (a *) x = δ a x · a *

infixl 30 _*


_∈_ : ∀ {A} → List A → Lang ω A → Bool
[]      ∈ a = ν a
(x ∷ w) ∈ a = w ∈ δ a x


⟦_⟧ : ∀ {i} → Bool → Lang i Bool
ν ⟦ _     ⟧       = false
δ ⟦ false ⟧ false = ε
δ ⟦ true  ⟧ true  = ε
δ ⟦ false ⟧ true  = ∅
δ ⟦ true  ⟧ false = ∅


bip-bop : Lang ω Bool
bip-bop = (⟦ true ⟧ · ⟦ false ⟧)*


test₁ : (true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ []) ∈ bip-bop ≡ true
test₁ = refl

test₂ : (true ∷ false ∷ true ∷ false ∷ true ∷ []) ∈ bip-bop ≡ false
test₂ = refl

test₃ : (true ∷ true ∷ false ∷ []) ∈ bip-bop ≡ false
test₃ = refl
