module Instances where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (refl)

open import Structures using (Shaped)

VecShaped : Shaped ℕ Vec
VecShaped = record
  { arity = id
  ; content = id
  ; fill = λ _ → id
  ; isShaped = record
    { content-fill = λ _ → refl
    ; fill-content = λ _ _ → refl
    } }
