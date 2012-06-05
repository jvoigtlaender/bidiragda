module BFF where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe ; just ; nothing ; maybe′)
open import Data.List using (List ; [] ; _∷_ ; map ; length)
open import Data.Vec using (Vec ; toList ; fromList ; tabulate) renaming (lookup to lookupVec)
open import Function using (id ; _∘_ ; flip)

open import FinMap
open import CheckInsert

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
_>>=_ = flip (flip maybe′ nothing)

fmap : {A B : Set} → (A → B) → Maybe A → Maybe B
fmap f = maybe′ (λ a → just (f a)) nothing

module ListBFF where

  assoc : {A : Set} {n : ℕ} → EqInst A → List (Fin n) → List A → Maybe (FinMapMaybe n A)
  assoc _  []       []       = just empty
  assoc eq (i ∷ is) (b ∷ bs) = (assoc eq is bs) >>= (checkInsert eq i b)
  assoc _  _        _        = nothing

  enumerate : {A : Set} → (l : List A) → List (Fin (length l))
  enumerate l = toList (tabulate id)

  denumerate : {A : Set} (l : List A) → Fin (length l) → A
  denumerate l = flip lookupVec (fromList l)

  bff : ({A : Set} → List A → List A) → ({B : Set} → EqInst B → List B → List B → Maybe (List B))
  bff get eq s v = let s′ = enumerate s
                       g  = fromFunc (denumerate s)
                       h  = assoc eq (get s′) v
                       h′ = fmap (flip union g) h
                   in fmap (flip map s′ ∘ flip lookup) h′
