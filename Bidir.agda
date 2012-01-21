module Bidir where

open import Data.Bool hiding (_≟_)
open import Data.Nat
open import Data.Fin
open import Data.Maybe
open import Data.List hiding (replicate)
open import Data.Vec hiding (map ; zip) renaming (lookup to lookupVec)
open import Data.Product hiding (zip ; map)
open import Function
open import Relation.Nullary
open import Relation.Binary.Core

module FinMap where

  FinMapMaybe : ℕ → Set → Set
  FinMapMaybe n A = Vec (Maybe A) n

  lookupM : {A : Set} {n : ℕ} → Fin n → FinMapMaybe n A → Maybe A
  lookupM = lookupVec

  insert : {A : Set} {n : ℕ} → Fin n → A → FinMapMaybe n A → FinMapMaybe n A
  insert f a m = m [ f ]≔ (just a)

  empty : {A : Set} {n : ℕ} → FinMapMaybe n A
  empty = replicate nothing

  fromAscList : {A : Set} {n : ℕ} → List (Fin n × A) → FinMapMaybe n A
  fromAscList []             = empty
  fromAscList ((f , a) ∷ xs) = insert f a (fromAscList xs)

  FinMap : ℕ → Set → Set
  FinMap n A = Vec A n

  lookup : {A : Set} {n : ℕ} → Fin n → FinMap n A → A
  lookup = lookupVec

  fromFunc : {A : Set} {n : ℕ} → (Fin n → A) → FinMap n A
  fromFunc = tabulate

  union : {A : Set} {n : ℕ} → FinMapMaybe n A → FinMap n  A → FinMap n A
  union m1 m2 = tabulate (λ f → maybe′ id (lookup f m2) (lookupM f m1))

open FinMap

checkInsert : {A : Set} {n : ℕ} → ((x y : A) → Dec (x ≡ y)) → Fin n → A → FinMapMaybe n A → Maybe (FinMapMaybe n A)
checkInsert eq i b m with lookupM i m
checkInsert eq i b m | just c with eq b c
checkInsert eq i b m | just .b | yes refl = just m
checkInsert eq i b m | just c  | no ¬p    = nothing
checkInsert eq i b m | nothing = just (insert i b m)

assoc : {A : Set} {n : ℕ} → ((x y : A) → Dec (x ≡ y)) → List (Fin n) → List A → Maybe (FinMapMaybe n A)
assoc _  []       []       = just empty
assoc eq (i ∷ is) (b ∷ bs) = maybe′ (checkInsert eq i b) nothing (assoc eq is bs)
assoc _  _        _        = nothing

generate : {A : Set} {n : ℕ} → (Fin n → A) → List (Fin n) → FinMapMaybe n A
generate f is = fromAscList (zip is (map f is))

lemma-1 : {τ : Set} {n : ℕ} → (eq : (x y : τ) → Dec (x ≡ y)) → (f : Fin n → τ) → (is : List (Fin n)) → assoc eq is (map f is) ≡ just (generate f is)
lemma-1 eq f []        = refl
lemma-1 eq f (i ∷ is′) = {!!}

idrange : (n : ℕ) → List (Fin n)
idrange n = toList (tabulate id)

bff : ({A : Set} → List A → List A) → ({B : Set} → ((x y : B) → Dec (x ≡ y)) → List B → List B → Maybe (List B))
bff get eq s v = let s′ = idrange (length s)
                     g  = fromFunc (λ f → lookupVec f (fromList s))
                     h  = assoc eq (get s′) v
                     h′ = maybe′ (λ jh → just (union jh g)) nothing h
                 in maybe′ (λ jh′ → just (map (flip lookup jh′) s′)) nothing h′
