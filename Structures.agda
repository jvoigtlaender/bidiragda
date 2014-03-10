module Structures where

open import Category.Functor using (RawFunctor ; module RawFunctor)
open import Category.Monad using (module RawMonad)
open import Data.Maybe using (Maybe) renaming (monad to MaybeMonad)
open import Data.Nat using (ℕ)
open import Data.Vec as V using (Vec)
import Data.Vec.Properties as VP
open import Function using (_∘_ ; flip ; id)
open import Function.Equality using (_⟶_ ; _⇨_ ; _⟨$⟩_)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality as P using (_≗_ ; _≡_ ; refl ; module ≡-Reasoning)

open import Generic using (sequenceV)

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

record IsShaped (S : Set)
                (C : Set → S → Set)
                (arity : S → ℕ)
                (content : {α : Set} {s : S} → C α s → Vec α (arity s))
                (fill : {α : Set} → (s : S) → Vec α (arity s) → C α s)
                : Set₁ where
  field
    content-fill : {α : Set} {s : S} → (c : C α s) → fill s (content c) ≡ c
    fill-content : {α : Set} → (s : S) → (v : Vec α (arity s)) → content (fill s v) ≡ v

  fmap : {α β : Set} → (f : α → β) → {s : S} → C α s → C β s
  fmap f {s} c = fill s (V.map f (content c))

  isFunctor : (s : S) → IsFunctor (flip C s) (λ f → fmap f)
  isFunctor s = record
    { cong = λ g≗h c → P.cong (fill s) (VP.map-cong g≗h (content c))
    ; identity = λ c → begin
        fill s (V.map id (content c))
          ≡⟨ P.cong (fill s) (VP.map-id (content c)) ⟩
        fill s (content c)
          ≡⟨ content-fill c ⟩
        c ∎
    ; composition = λ g h c → P.cong (fill s) (begin
        V.map (g ∘ h) (content c)
          ≡⟨ VP.map-∘ g h (content c) ⟩
        V.map g (V.map h (content c))
          ≡⟨ P.cong (V.map g) (P.sym (fill-content s (V.map h (content c)))) ⟩
        V.map g (content (fill s (V.map h (content c)))) ∎)
    } where open ≡-Reasoning

  fmap-content : {α β : Set} → (f : α → β) → {s : S} → content {β} {s} ∘ fmap f ≗ V.map f ∘ content
  fmap-content f c = fill-content _ (V.map f (content c))
  fill-fmap : {α β : Set} → (f : α → β) → (s : S) → fmap f ∘ fill s ≗ fill s ∘ V.map f
  fill-fmap f s v = P.cong (fill s ∘ V.map f) (fill-content s v)

  sequence : {α : Set} {s : S} → C (Maybe α) s → Maybe (C α s)
  sequence {s = s} c = fill s <$> sequenceV (content c)
    where open RawMonad MaybeMonad

record Shaped (S : Set) (C : Set → S → Set) : Set₁ where
  field
    arity : S → ℕ
    content : {α : Set} {s : S} → C α s → Vec α (arity s)
    fill : {α : Set} → (s : S) → Vec α (arity s) → C α s

    isShaped : IsShaped S C arity content fill

  open IsShaped isShaped public
