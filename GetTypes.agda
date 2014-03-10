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
open import Structures using (Shaped ; module Shaped)
open import Instances using (VecShaped)

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

module PartialShapeVec where
  record Get : Set₁ where
    field
      Shape : Set
      Container : Set → Shape → Set
      ShapeT : Shaped Shape Container

      I : Setoid ℓ₀ ℓ₀
      gl₁ : I ↪ EqSetoid Shape
      gl₂ : I ⟶ EqSetoid ℕ

    |I|   = Setoid.Carrier I
    |gl₁| = _⟨$⟩_ (to gl₁)
    |gl₂| = _⟨$⟩_ gl₂

    open Shaped ShapeT using (fmap)

    field
      get : {A : Set} {i : |I|} → Container A (|gl₁| i) → Vec A (|gl₂| i)
      free-theorem : {α β : Set} → (f : α → β) → {i : |I|} → get {_} {i} ∘ fmap f ≗ mapV f ∘ get

    open Shaped ShapeT public

PartialVecVec-to-PartialShapeVec : PartialVecVec.Get → PartialShapeVec.Get
PartialVecVec-to-PartialShapeVec G = record
  { ShapeT       = VecShaped
  ; I            = I
  ; gl₁          = gl₁
  ; gl₂          = gl₂
  ; get          = get
  ; free-theorem = free-theorem
  } where open PartialVecVec.Get G

module PartialShapeShape where
  record Get : Set₁ where
    field
      SourceShape : Set
      SourceContainer : Set → SourceShape → Set
      SourceShapeT : Shaped SourceShape SourceContainer

      ViewShape : Set
      ViewContainer : Set → ViewShape → Set
      ViewShapeT : Shaped ViewShape ViewContainer

      I : Setoid ℓ₀ ℓ₀
      gl₁ : I ↪ EqSetoid SourceShape
      gl₂ : I ⟶ EqSetoid ViewShape

    |I|   = Setoid.Carrier I
    |gl₁| = _⟨$⟩_ (to gl₁)
    |gl₂| = _⟨$⟩_ gl₂

    open Shaped SourceShapeT using () renaming (fmap to fmapS)
    open Shaped ViewShapeT using () renaming (fmap to fmapV)

    field
      get : {A : Set} {i : |I|} → SourceContainer A (|gl₁| i) → ViewContainer A (|gl₂| i)
      free-theorem : {α β : Set} → (f : α → β) → {i : |I|} → get {_} {i} ∘ fmapS f ≗ fmapV f ∘ get

    open Shaped SourceShapeT public using () renaming (fmap to fmapS)
    open Shaped ViewShapeT public using () renaming (fmap to fmapV)

PartialShapeVec-to-PartialShapeShape : PartialShapeVec.Get → PartialShapeShape.Get
PartialShapeVec-to-PartialShapeShape G = record
  { SourceShapeT = ShapeT
  ; ViewShapeT   = VecShaped
  ; I            = I
  ; gl₁          = gl₁
  ; gl₂          = gl₂
  ; get          = get
  ; free-theorem = free-theorem
  } where open PartialShapeVec.Get G
