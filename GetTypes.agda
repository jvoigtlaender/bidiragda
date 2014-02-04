module GetTypes where

open import Level using () renaming (zero to ℓ₀)
open import Data.Nat using (ℕ)
open import Data.List using (List ; map)
open import Data.Vec using (Vec) renaming (map to mapV)
open import Function using (_∘_)
open import Function.Equality using (_⟶_ ; _⟨$⟩_)
open import Function.Injection using (module Injection) renaming (Injection to _↪_ ; id to id↪)
open import Relation.Binary.PropositionalEquality using (_≗_) renaming (setoid to EqSetoid)
open import Relation.Binary using (Setoid)
open Injection using (to)

open import Generic using (≡-to-Π)

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

module PartialVecVec where
  record Get : Set₁ where
    field
      I : Setoid ℓ₀ ℓ₀
      gl₁ : I ↪ EqSetoid ℕ
      gl₂ : I ⟶ EqSetoid ℕ

    |I|   = Setoid.Carrier I
    |gl₁| = _⟨$⟩_ (to gl₁)
    |gl₂| = _⟨$⟩_ gl₂

    field
      get : {A : Set} {i : |I|} → Vec A (|gl₁| i) → Vec A (|gl₂| i)
      free-theorem : {α β : Set} → (f : α → β) → {i : |I|} → get {_} {i} ∘ mapV f ≗ mapV f ∘ get

VecVec-to-PartialVecVec : VecVec.Get → PartialVecVec.Get
VecVec-to-PartialVecVec G = record
  { I = EqSetoid ℕ
  ; gl₁ = id↪
  ; gl₂ = ≡-to-Π getlen
  ; get = get
  ; free-theorem = free-theorem
  } where open VecVec.Get G
