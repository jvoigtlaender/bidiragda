module Instances where

open import Level using () renaming (zero to ℓ₀)
open import Category.Functor using (RawFunctor)
open import Data.Maybe as M using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec)
import Data.Vec.Equality
open Data.Vec.Equality.PropositionalEquality using () renaming (to-≡ to VecEq-to-≡)
open import Function using (_∘_ ; id)
open import Relation.Binary using (Setoid ; module Setoid)
open import Relation.Binary.Indexed using (_at_) renaming (Setoid to ISetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_ ; _≗_ ; module ≡-Reasoning)

open Setoid using () renaming (_≈_ to _∋_≈_)

open import Generic using (VecISetoid)
open import Structures using (Functor ; Shaped ; module Shaped)

MaybeFunctor : Functor Maybe
MaybeFunctor = record
  { rawfunctor = M.functor
  ; isFunctor = record
    { cong = cong
    ; identity = identity
    ; composition = composition
    } }
  where _<$>_ = RawFunctor._<$>_ M.functor

        cong : {α β : Set} {g h : α → β} → g ≗ h → _<$>_ g ≗ _<$>_ h
        cong g≗h (M.just x) = P.cong M.just (g≗h x)
        cong g≗h M.nothing  = P.refl

        identity : {α : Set} → _<$>_ {α} id ≗ id
        identity (M.just x) = P.refl
        identity M.nothing  = P.refl

        composition : {α β γ : Set} → (g : β → γ) → (h : α → β) → _<$>_ (g ∘ h) ≗ _<$>_ g ∘ _<$>_ h
        composition g h (M.just x) = P.refl
        composition g h M.nothing  = P.refl

VecShaped : Shaped ℕ Vec
VecShaped = record
  { arity = id
  ; content = id
  ; fill = λ _ → id
  ; isShaped = record
    { content-fill = λ _ → P.refl
    ; fill-content = λ _ _ → P.refl
    } }

ShapedISetoid : (S : Setoid ℓ₀ ℓ₀) {C : Set → (Setoid.Carrier S) → Set} → Shaped (Setoid.Carrier S) C → Setoid ℓ₀ ℓ₀ → ISetoid (Setoid.Carrier S) ℓ₀ ℓ₀
ShapedISetoid S {C} ShapeT α = record
  { Carrier = C (Setoid.Carrier α)
  ; _≈_ = λ {s₁} {s₂} c₁ c₂ → S ∋ s₁ ≈ s₂ × ISetoid._≈_ (VecISetoid α) (content c₁) (content c₂)
  ; isEquivalence = record
    { refl = Setoid.refl S , ISetoid.refl (VecISetoid α)
    ; sym = λ p → Setoid.sym S (proj₁ p) , ISetoid.sym (VecISetoid α) (proj₂ p)
    ; trans = λ p q → Setoid.trans S (proj₁ p) (proj₁ q) , ISetoid.trans (VecISetoid α) (proj₂ p) (proj₂ q)
    } } where open Shaped ShapeT

Shaped≈-to-≡ : {S : Set} {C : Set → S → Set} → (ShapeT : Shaped S C) → (α : Set) → {s : S} {x y : C α s} → ShapedISetoid (P.setoid S) ShapeT (P.setoid α) at s ∋ x ≈ y → x ≡ y
Shaped≈-to-≡ ShapeT α {s} {x} {y} (shape≈ , content≈) = begin
  x
    ≡⟨ P.sym (content-fill x) ⟩
  fill s (content x)
    ≡⟨ P.cong (fill s) (VecEq-to-≡ content≈) ⟩
  fill s (content y)
    ≡⟨ content-fill y ⟩
  y ∎
  where open ≡-Reasoning
        open Shaped ShapeT
