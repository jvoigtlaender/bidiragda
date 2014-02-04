module BFF where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Level using () renaming (zero to ℓ₀)
import Category.Monad
import Category.Functor
open import Data.Maybe using (Maybe ; just ; nothing ; maybe′)
open Category.Monad.RawMonad {Level.zero} Data.Maybe.monad using (_>>=_)
open Category.Functor.RawFunctor {Level.zero} Data.Maybe.functor using (_<$>_)
open import Data.List using (List ; [] ; _∷_ ; map ; length)
open import Data.Vec using (Vec ; toList ; fromList ; tabulate ; allFin) renaming (lookup to lookupV ; map to mapV ; [] to []V ; _∷_ to _∷V_)
open import Function using (id ; _∘_ ; flip)
open import Function.Equality using (_⟶_ ; _⟨$⟩_)
open import Function.Injection using (module Injection) renaming (Injection to _↪_ ; id to id↪)
open import Relation.Binary using (Setoid ; DecSetoid ; module DecSetoid)
open import Relation.Binary.PropositionalEquality using (cong) renaming (setoid to EqSetoid)
open Injection using (to)

open import FinMap
open import Generic using (mapMV ; ≡-to-Π)
import CheckInsert
open import GetTypes using (VecVec-to-PartialVecVec)

module PartialVecBFF (A : DecSetoid ℓ₀ ℓ₀) where
  open GetTypes.PartialVecVec public using (Get)
  open module A = DecSetoid A using (Carrier) renaming (_≟_ to deq)
  open CheckInsert A

  assoc : {n m : ℕ} → Vec (Fin n) m → Vec Carrier m → Maybe (FinMapMaybe n Carrier)
  assoc []V       []V       = just empty
  assoc (i ∷V is) (b ∷V bs) = (assoc is bs) >>= (checkInsert i b)

  enumerate : {n : ℕ} → Vec Carrier n → Vec (Fin n) n
  enumerate _ = tabulate id

  denumerate : {n : ℕ} → Vec Carrier n → Fin n → Carrier
  denumerate = flip lookupV


  bff : (G : Get) → ({i : Setoid.Carrier (Get.I G)} → Vec Carrier (to (Get.gl₁ G) ⟨$⟩ i) → Vec Carrier ((Get.gl₂ G) ⟨$⟩ i) → Maybe (Vec Carrier (to (Get.gl₁ G) ⟨$⟩ i)))
  bff G s v = let   s′ = enumerate s
                    t′ = Get.get G s′
                    g  = fromFunc (denumerate s)
                    g′ = delete-many t′ g
                    h  = assoc t′ v
                    h′ = (flip union g′) <$> h
                in h′ >>= flip mapMV s′ ∘ flip lookupV

module VecBFF (A : DecSetoid ℓ₀ ℓ₀) where
  open GetTypes.VecVec public using (Get)
  open module A = DecSetoid A using (Carrier) renaming (_≟_ to deq)
  open CheckInsert A

  open PartialVecBFF A public using (assoc ; enumerate ; denumerate)

  bff : (G : Get) → ({n : ℕ} → Vec Carrier n → Vec Carrier (Get.getlen G n) → Maybe (Vec Carrier n))
  bff G = PartialVecBFF.bff A (VecVec-to-PartialVecVec G)
