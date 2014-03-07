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
open import Data.Vec using (Vec ; toList ; fromList ; allFin) renaming (lookup to lookupV ; map to mapV ; [] to []V ; _∷_ to _∷V_)
open import Function using (_∘_ ; flip)
open import Relation.Binary using (Setoid ; DecSetoid ; module DecSetoid)

open import FinMap
open import Generic using (sequenceV ; ≡-to-Π)
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
  enumerate {n} _ = allFin n

  enumeratel : (n : ℕ) → Vec (Fin n) n
  enumeratel = allFin

  denumerate : {n : ℕ} → Vec Carrier n → Fin n → Carrier
  denumerate = flip lookupV

  bff : (G : Get) → {i : Get.|I| G} → (j : Get.|I| G) → Vec Carrier (Get.|gl₁| G i) → Vec Carrier (Get.|gl₂| G j) → Maybe (Vec (Maybe Carrier) (Get.|gl₁| G j))
  bff G i s v = let s′ = enumerate s
                    t′ = Get.get G s′
                    g  = fromFunc (denumerate s)
                    g′ = delete-many t′ g
                    t  = enumeratel (Get.|gl₁| G i)
                    h  = assoc (Get.get G t) v
                    h′ = (flip union (reshape g′ (Get.|gl₁| G i))) <$> h
                in (flip mapV t ∘ flip lookupM) <$> h′

  sbff : (G : Get) → {i : Get.|I| G} → (j : Get.|I| G) → Vec Carrier (Get.|gl₁| G i) → Vec Carrier (Get.|gl₂| G j) → Maybe (Vec Carrier (Get.|gl₁| G j))
  sbff G j s v = bff G j s v >>= sequenceV

module VecBFF (A : DecSetoid ℓ₀ ℓ₀) where
  open GetTypes.VecVec public using (Get)
  open module A = DecSetoid A using (Carrier) renaming (_≟_ to deq)
  open CheckInsert A

  open PartialVecBFF A public using (assoc ; enumerate ; denumerate)

  bff : (G : Get) → {n : ℕ} → (m : ℕ) → Vec Carrier n → Vec Carrier (Get.getlen G m) → Maybe (Vec (Maybe Carrier) m)
  bff G = PartialVecBFF.bff A (VecVec-to-PartialVecVec G)

  sbff : (G : Get) → {n : ℕ} → (m : ℕ) → Vec Carrier n → Vec Carrier (Get.getlen G m) → Maybe (Vec Carrier m)
  sbff G = PartialVecBFF.sbff A (VecVec-to-PartialVecVec G)
