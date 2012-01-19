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

  FinMap : ℕ → Set → Set
  FinMap n A = Vec (Maybe A) n

  lookup : {A : Set} {n : ℕ} → Fin n → FinMap n A → Maybe A
  lookup = lookupVec

  notMember : {A : Set} → {n : ℕ} → Fin n → FinMap n A → Bool
  notMember n = not ∘ maybeToBool ∘ lookup n

  insert : {A : Set} {n : ℕ} → Fin n → A → FinMap n A → FinMap n A
  insert f a m = m [ f ]≔ (just a)

  empty : {A : Set} {n : ℕ} → FinMap n A
  empty = replicate nothing

  fromAscList : {A : Set} {n : ℕ} → List (Fin n × A) → FinMap n A
  fromAscList []       = empty
  fromAscList ((f , a) ∷ xs) = insert f a (fromAscList xs)

  union : {A : Set} {n : ℕ} → FinMap n A → FinMap n A → FinMap n A
  union m1 m2 = tabulate (λ f → maybe′ just (lookup f m2) (lookup f m1))

open FinMap

checkInsert : {A : Set} {n : ℕ} → ((x y : A) → Dec (x ≡ y)) → Fin n → A → FinMap n A → Maybe (FinMap n A)
checkInsert eq i b m with lookup i m
checkInsert eq i b m | just c with eq b c
checkInsert eq i b m | just .b | yes refl = just m
checkInsert eq i b m | just c  | no ¬p    = nothing
checkInsert eq i b m | nothing = just (insert i b m)

assoc : {A : Set} {n : ℕ} → ((x y : A) → Dec (x ≡ y)) → List (Fin n) → List A → Maybe (FinMap n A)
assoc _  []       []       = just empty
assoc eq (i ∷ is) (b ∷ bs) = maybe′ (checkInsert eq i b) nothing (assoc eq is bs)
assoc _  _        _        = nothing

generate : {A : Set} {n : ℕ} → (Fin n → A) → List (Fin n) → FinMap n A
generate f []       = empty
generate f (n ∷ ns) = insert n (f n) (generate f ns)

lemma-1 : {τ : Set} {n : ℕ} → (eq : (x y : τ) → Dec (x ≡ y)) → (f : Fin n → τ) → (is : List (Fin n)) → assoc eq is (map f is) ≡ just (generate f is)
lemma-1 eq f []        = refl
lemma-1 eq f (i ∷ is′) = {!!}

idrange : (n : ℕ) → List (Fin n)
idrange n = toList (tabulate id)

bff : ({A : Set} → List A → List A) → ({B : Set} → ((x y : B) → Dec (x ≡ y)) → List B → List B → Maybe (List B))
bff get eq s v = let s′ = idrange (length s)
                     g  = fromAscList (zip s′ s)
                     h  = assoc eq (get s′) v
                     h′ = maybe′ (λ jh → just (union jh g)) nothing h
                 in maybe′ (λ jh′ → just (map {!!} s′)) nothing h′
