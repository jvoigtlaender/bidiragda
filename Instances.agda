module Instances where

open import Category.Functor using (RawFunctor)
open import Data.Maybe as M using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Function using (_∘_ ; id)
open import Relation.Binary.PropositionalEquality as P using (_≗_ ; refl)

open import Structures using (Functor ; Shaped)

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
        cong g≗h M.nothing  = refl

        identity : {α : Set} → _<$>_ {α} id ≗ id
        identity (M.just x) = refl
        identity M.nothing  = refl

        composition : {α β γ : Set} → (g : β → γ) → (h : α → β) → _<$>_ (g ∘ h) ≗ _<$>_ g ∘ _<$>_ h
        composition g h (M.just x) = refl
        composition g h M.nothing = refl

VecShaped : Shaped ℕ Vec
VecShaped = record
  { arity = id
  ; content = id
  ; fill = λ _ → id
  ; isShaped = record
    { content-fill = λ _ → refl
    ; fill-content = λ _ _ → refl
    } }
