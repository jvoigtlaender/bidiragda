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
open import Structures using (Shaped ; module Shaped)
open import Instances using (VecShaped)
import CheckInsert
open import GetTypes using (VecVec-to-PartialVecVec ; PartialVecVec-to-PartialShapeShape)

module PartialShapeBFF (A : DecSetoid ℓ₀ ℓ₀) where
  open GetTypes.PartialShapeShape public using (Get ; module Get)
  open module A = DecSetoid A using (Carrier) renaming (_≟_ to deq)
  open CheckInsert A

  assoc : {n m : ℕ} → Vec (Fin n) m → Vec Carrier m → Maybe (FinMapMaybe n Carrier)
  assoc []V       []V       = just empty
  assoc (i ∷V is) (b ∷V bs) = (assoc is bs) >>= (checkInsert i b)

  enumerate : {S : Set} {C : Set → S → Set} → (ShapeT : Shaped S C) → (s : S) → C (Fin (Shaped.arity ShapeT s)) s
  enumerate ShapeT s = fill s (allFin (arity s))
    where open Shaped ShapeT

  denumerate : {S : Set} {C : Set → S → Set} → (ShapeT : Shaped S C) → {α : Set} {s : S} → (c : C α s) → Fin (Shaped.arity ShapeT s) → α
  denumerate ShapeT c = flip lookupV (Shaped.content ShapeT c)

  bff : (G : Get) → {i : Get.I G} → (j : Get.I G) → Get.SourceContainer G Carrier (Get.gl₁ G i) → Get.ViewContainer G Carrier (Get.gl₂ G j) → Maybe (Get.SourceContainer G (Maybe Carrier) (Get.gl₁ G j))
  bff G {i} j s v = let s′ = enumerate SourceShapeT (gl₁ i)
                        t′ = get s′
                        g  = fromFunc (denumerate SourceShapeT s)
                        g′ = delete-many (Shaped.content ViewShapeT t′) g
                        t  = enumerate SourceShapeT (gl₁ j)
                        h  = assoc (Shaped.content ViewShapeT (get t)) (Shaped.content ViewShapeT v)
                        h′ = (flip union (reshape g′ (Shaped.arity SourceShapeT (gl₁ j)))) <$> h
                    in ((λ f → fmapS f t) ∘ flip lookupM) <$> h′
    where open Get G

  sbff : (G : Get) → {i : Get.I G} → (j : Get.I G) → Get.SourceContainer G Carrier (Get.gl₁ G i) → Get.ViewContainer G Carrier (Get.gl₂ G j) → Maybe (Get.SourceContainer G Carrier (Get.gl₁ G j))
  sbff G j s v = bff G j s v >>= Shaped.sequence (Get.SourceShapeT G)

module PartialVecBFF (A : DecSetoid ℓ₀ ℓ₀) where
  open GetTypes.PartialVecVec public using (Get)
  open module A = DecSetoid A using (Carrier) renaming (_≟_ to deq)
  open CheckInsert A

  open PartialShapeBFF A public using (assoc)

  enumerate : {n : ℕ} → Vec Carrier n → Vec (Fin n) n
  enumerate {n} _ = PartialShapeBFF.enumerate A VecShaped n

  enumeratel : (n : ℕ) → Vec (Fin n) n
  enumeratel = PartialShapeBFF.enumerate A VecShaped

  denumerate : {n : ℕ} → Vec Carrier n → Fin n → Carrier
  denumerate = PartialShapeBFF.denumerate A VecShaped

  bff : (G : Get) → {i : Get.I G} → (j : Get.I G) → Vec Carrier (Get.gl₁ G i) → Vec Carrier (Get.gl₂ G j) → Maybe (Vec (Maybe Carrier) (Get.gl₁ G j))
  bff G j s v = PartialShapeBFF.bff A (PartialVecVec-to-PartialShapeShape G) j s v

  sbff : (G : Get) → {i : Get.I G} → (j : Get.I G) → Vec Carrier (Get.gl₁ G i) → Vec Carrier (Get.gl₂ G j) → Maybe (Vec Carrier (Get.gl₁ G j))
  sbff  G j s v = PartialShapeBFF.sbff A (PartialVecVec-to-PartialShapeShape G) j s v

module VecBFF (A : DecSetoid ℓ₀ ℓ₀) where
  open GetTypes.VecVec public using (Get)
  open module A = DecSetoid A using (Carrier) renaming (_≟_ to deq)
  open CheckInsert A

  open PartialVecBFF A public using (assoc ; enumerate ; denumerate)

  bff : (G : Get) → {n : ℕ} → (m : ℕ) → Vec Carrier n → Vec Carrier (Get.getlen G m) → Maybe (Vec (Maybe Carrier) m)
  bff G = PartialVecBFF.bff A (VecVec-to-PartialVecVec G)

  sbff : (G : Get) → {n : ℕ} → (m : ℕ) → Vec Carrier n → Vec Carrier (Get.getlen G m) → Maybe (Vec Carrier m)
  sbff G = PartialVecBFF.sbff A (VecVec-to-PartialVecVec G)
