module BFF where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Level
import Category.Monad
import Category.Functor
open import Data.Maybe using (Maybe ; just ; nothing ; maybe′)
open Category.Monad.RawMonad {Level.zero} Data.Maybe.monad using (_>>=_)
open Category.Functor.RawFunctor {Level.zero} Data.Maybe.functor using (_<$>_)
open import Data.List using (List ; [] ; _∷_ ; map ; length)
open import Data.Vec using (Vec ; toList ; fromList ; tabulate ; allFin) renaming (lookup to lookupV ; map to mapV ; [] to []V ; _∷_ to _∷V_)
open import Function using (id ; _∘_ ; flip)
open import Relation.Binary.Core using (Decidable ; _≡_)

open import FinMap
import CheckInsert
import FreeTheorems

module ListBFF (Carrier : Set) (deq : Decidable {A = Carrier} _≡_) where
  open FreeTheorems.ListList public using (get-type)
  open CheckInsert Carrier deq

  assoc : {n : ℕ} → List (Fin n) → List Carrier → Maybe (FinMapMaybe n Carrier)
  assoc []       []       = just empty
  assoc (i ∷ is) (b ∷ bs) = (assoc is bs) >>= (checkInsert i b)
  assoc _        _        = nothing

  enumerate : (l : List Carrier) → List (Fin (length l))
  enumerate l = toList (tabulate id)

  denumerate : (l : List Carrier) → Fin (length l) → Carrier
  denumerate l = flip lookupV (fromList l)

  bff : get-type → (List Carrier → List Carrier → Maybe (List Carrier))
  bff get s v = let s′ = enumerate s
                    g  = fromFunc (denumerate s)
                    h  = assoc (get s′) v
                    h′ = (flip union g) <$> h
                in (flip map s′ ∘ flip lookup) <$> h′

module VecBFF (Carrier : Set) (deq : Decidable {A = Carrier} _≡_) where
  open FreeTheorems.VecVec public using (get-type)
  open CheckInsert Carrier deq

  assoc : {n m : ℕ} → Vec (Fin n) m → Vec Carrier m → Maybe (FinMapMaybe n Carrier)
  assoc []V       []V       = just empty
  assoc (i ∷V is) (b ∷V bs) = (assoc is bs) >>= (checkInsert i b)

  enumerate : {n : ℕ} → Vec Carrier n → Vec (Fin n) n
  enumerate _ = tabulate id

  denumerate : {n : ℕ} → Vec Carrier n → Fin n → Carrier
  denumerate = flip lookupV

  bff : {getlen : ℕ → ℕ} → (get-type getlen) → ({n : ℕ} → Vec Carrier n → Vec Carrier (getlen n) → Maybe (Vec Carrier n))
  bff get s v = let s′ = enumerate s
                    g  = fromFunc (denumerate s)
                    h  = assoc (get s′) v
                    h′ = (flip union g) <$> h
                in (flip mapV s′ ∘ flip lookupV) <$> h′
