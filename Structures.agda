module Structures where

open import Category.Functor using (RawFunctor ; module RawFunctor)
open import Function using (_∘_ ; id)
open import Function.Equality using (_⟶_ ; _⇨_ ; _⟨$⟩_)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality as P using (_≗_ ; _≡_ ; refl)

record IsFunctor (F : Set → Set) (f : {α β : Set} → (α →  β) → F α → F β) : Set₁ where
  field
    cong : {α β : Set} → f {α} {β} Preserves _≗_ ⟶ _≗_
    identity : {α : Set} → f {α} id ≗ id
    composition : {α β γ : Set} → (g : β → γ) → (h : α → β) →
                  f (g ∘ h) ≗ f g ∘ f h

  isCongruence : {α β : Set} → (P.setoid α ⇨ P.setoid β) ⟶ P.setoid (F α) ⇨ P.setoid (F β)
  isCongruence {α} {β} = record
    { _⟨$⟩_ = λ g → record
      { _⟨$⟩_ = f (_⟨$⟩_ g)
      ; cong = P.cong (f (_⟨$⟩_ g))
      }
    ; cong = λ {g} {h} g≗h {x} x≡y → P.subst (λ z → f (_⟨$⟩_ g) x ≡ f (_⟨$⟩_ h) z) x≡y (cong (λ _ → g≗h refl) x)
    }

record Functor (f : Set → Set) : Set₁ where
  field
    rawfunctor : RawFunctor f
    isFunctor : IsFunctor f (RawFunctor._<$>_ rawfunctor)

  open RawFunctor rawfunctor public
  open IsFunctor isFunctor public
