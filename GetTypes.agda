module GetTypes where

open import Level using () renaming (zero to ℓ₀)
open import Data.Nat using (ℕ)
open import Data.List using (List ; map)
open import Data.Vec using (Vec) renaming (map to mapV)
open import Function using (_∘_ ; id)
open import Relation.Binary.PropositionalEquality using (_≗_)

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
      I : Set
      gl₁ : I → ℕ
      gl₂ : I → ℕ
      get : {A : Set} {i : I} → Vec A (gl₁ i) → Vec A (gl₂ i)
      free-theorem : {α β : Set} → (f : α → β) → {i : I} → get {_} {i} ∘ mapV f ≗ mapV f ∘ get

VecVec-to-PartialVecVec : VecVec.Get → PartialVecVec.Get
VecVec-to-PartialVecVec G = record
  { I = ℕ
  ; gl₁ = id
  ; gl₂ = getlen
  ; get = get
  ; free-theorem = free-theorem
  } where open VecVec.Get G

module PartialShapeShape where
  record Get : Set₁ where
    field
      SourceShape : Set
      SourceContainer : Set → SourceShape → Set
      SourceShapeT : Shaped SourceShape SourceContainer

      ViewShape : Set
      ViewContainer : Set → ViewShape → Set
      ViewShapeT : Shaped ViewShape ViewContainer

      I : Set
      gl₁ : I → SourceShape
      gl₂ : I → ViewShape

    open Shaped SourceShapeT using () renaming (fmap to fmapS)
    open Shaped ViewShapeT using () renaming (fmap to fmapV)

    field
      get : {A : Set} {i : I} → SourceContainer A (gl₁ i) → ViewContainer A (gl₂ i)
      free-theorem : {α β : Set} → (f : α → β) → {i : I} → get {_} {i} ∘ fmapS f ≗ fmapV f ∘ get

    open Shaped SourceShapeT public using () renaming (fmap to fmapS)
    open Shaped ViewShapeT public using () renaming (fmap to fmapV)

PartialVecVec-to-PartialShapeShape : PartialVecVec.Get → PartialShapeShape.Get
PartialVecVec-to-PartialShapeShape G = record
  { SourceShapeT = VecShaped
  ; ViewShapeT   = VecShaped
  ; I            = I
  ; gl₁          = gl₁
  ; gl₂          = gl₂
  ; get          = get
  ; free-theorem = free-theorem
  } where open PartialVecVec.Get G
