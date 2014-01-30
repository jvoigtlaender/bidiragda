module FreeTheorems where

open import Data.Nat using (ℕ)
open import Data.List using (List ; map)
open import Data.Vec using (Vec) renaming (map to mapV)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≗_)

module ListList where
  get-type : Set₁
  get-type = {A : Set} → List A → List A

  record Get : Set₁ where
    field
      get : {A : Set} → List A → List A
      free-theorem : {α β : Set} → (f : α → β) → get ∘ map f ≗ map f ∘ get

  postulate
    free-theorem : (get : get-type) → {α β : Set} → (f : α → β) → get ∘ map f ≗ map f ∘ get

  assume-get : get-type → Get
  assume-get get = record { get = get; free-theorem = free-theorem get }

module VecVec where
  get-type : (ℕ → ℕ) → Set₁
  get-type getlen = {A : Set} {n : ℕ} → Vec A n → Vec A (getlen n)

  record Get : Set₁ where
    field
      getlen : ℕ → ℕ
      get : {A : Set} {n : ℕ} → Vec A n → Vec A (getlen n)
      free-theorem : {α β : Set} (f : α → β) {n : ℕ} → get {_} {n} ∘ mapV f ≗ mapV f ∘ get

  postulate
    free-theorem : {getlen : ℕ → ℕ} → (get : get-type getlen) → {α β : Set} → (f : α → β) → {n : ℕ} → get {_} {n} ∘ mapV f ≗ mapV f ∘ get

  assume-get : {getlen : ℕ → ℕ} → (get : get-type getlen) → Get
  assume-get {getlen} get = record { getlen = getlen; get = get; free-theorem = free-theorem get }
