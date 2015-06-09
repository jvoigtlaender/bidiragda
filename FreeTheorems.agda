module FreeTheorems where

open import Level using () renaming (zero to ℓ₀)
open import Data.Nat using (ℕ)
open import Data.List using (List ; map)
open import Data.Vec using (Vec) renaming (map to mapV)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≗_)

import GetTypes

module ListList where
  get-type : Set₁
  get-type = {A : Set} → List A → List A

  open GetTypes.ListList public

  postulate
    free-theorem : (get : get-type) → {α β : Set} → (f : α → β) → get ∘ map f ≗ map f ∘ get

  assume-get : get-type → Get
  assume-get get = record { get = get; free-theorem = free-theorem get }

module VecVec where
  get-type : (ℕ → ℕ) → Set₁
  get-type getlen = {A : Set} {n : ℕ} → Vec A n → Vec A (getlen n)

  open GetTypes.VecVec public

  postulate
    free-theorem : {getlen : ℕ → ℕ} → (get : get-type getlen) → {α β : Set} → (f : α → β) → {n : ℕ} → get {_} {n} ∘ mapV f ≗ mapV f ∘ get

  assume-get : {getlen : ℕ → ℕ} → (get : get-type getlen) → Get
  assume-get {getlen} get = record { getlen = getlen; get = get; free-theorem = free-theorem get }

module PartialVecVec where
  get-type : {I : Set} → (I → ℕ) → (I → ℕ) → Set₁
  get-type {I} gl₁ gl₂ = {A : Set} {i : I} → Vec A (gl₁ i) → Vec A (gl₂ i)

  open GetTypes.PartialVecVec public

  postulate
    free-theorem : {I : Set} → (gl₁ : I → ℕ) → (gl₂ : I → ℕ) (get : get-type gl₁ gl₂)  → {α β : Set} → (f : α → β) → {i : I} → get {_} {i} ∘ mapV f ≗ mapV f ∘ get

  assume-get : {I : Set} → (gl₁ : I → ℕ) → (gl₂ : I → ℕ) (get : get-type gl₁ gl₂) → Get
  assume-get {I} gl₁ gl₂ get = record { I = I; gl₁ = gl₁; gl₂ = gl₂; get = get; free-theorem = free-theorem gl₁ gl₂ get }
