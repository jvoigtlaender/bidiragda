module GetTypes where

open import Data.Nat using (ℕ)
open import Data.List using (List ; map)
open import Data.Vec using (Vec) renaming (map to mapV)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≗_)

module ListList where
  record Get : Set₁ where
    field
      get : {A : Set} → List A → List A
      free-theorem : {α β : Set} → (f : α → β) → get ∘ map f ≗ map f ∘ get

module VecVec where
  record Get : Set₁ where
    field
      getlen : ℕ → ℕ
      get : {A : Set} {n : ℕ} → Vec A n → Vec A (getlen n)
      free-theorem : {α β : Set} (f : α → β) {n : ℕ} → get {_} {n} ∘ mapV f ≗ mapV f ∘ get
