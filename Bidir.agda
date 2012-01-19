module Bidir where

open import Data.Bool hiding (_≟_)
open import Data.Nat
open import Data.Maybe
open import Data.List hiding (replicate)
open import Data.Product hiding (zip ; map)
open import Function
open import Relation.Nullary
open import Relation.Binary.Core

module NatMap where

  NatMap : Set → Set
  NatMap A = List (ℕ × A)

  lookup : {A : Set} → ℕ → NatMap A → Maybe A
  lookup n []       = nothing
  lookup n ((m , a) ∷ xs) with n ≟ m
  lookup n ((.n , a) ∷ xs) | yes refl = just a
  lookup n ((m , a) ∷ xs)  | no ¬p    = lookup n xs

  notMember : {A : Set} → ℕ → NatMap A → Bool
  notMember n m = not (maybeToBool (lookup n m))

  -- For now we simply prepend the element. This may lead to duplicates.
  insert : {A : Set} → ℕ → A → NatMap A → NatMap A
  insert n a m = (n , a) ∷ m

  fromAscList : {A : Set} → List (ℕ × A) → NatMap A
  fromAscList []       = []
  fromAscList ((n , a) ∷ xs) = insert n a (fromAscList xs)

  empty : {A : Set} → NatMap A
  empty = []

  union : {A : Set} → NatMap A → NatMap A → NatMap A
  union []       m = m
  union ((n , a) ∷ xs) m = insert n a (union xs m)

open NatMap

checkInsert : {A : Set} → ((x y : A) → Dec (x ≡ y)) → ℕ → A → NatMap A → Maybe (NatMap A)
checkInsert eq i b m with lookup i m
checkInsert eq i b m | just c with eq b c
checkInsert eq i b m | just .b | yes refl = just m
checkInsert eq i b m | just c  | no ¬p    = nothing
checkInsert eq i b m | nothing = just (insert i b m)

assoc : {A : Set} → ((x y : A) → Dec (x ≡ y)) → List ℕ → List A → Maybe (NatMap A)
assoc _  []       []       = just empty
assoc eq (i ∷ is) (b ∷ bs) = maybe′ (checkInsert eq i b) nothing (assoc eq is bs)
assoc _  _        _        = nothing

generate : {A : Set} → (ℕ → A) → List ℕ → NatMap A
generate f []       = empty
generate f (n ∷ ns) = insert n (f n) (generate f ns)

-- this lemma is probably wrong, because two different NatMaps may represent the same semantic value.
lemma-1 : {τ : Set} → (eq : (x y : τ) → Dec (x ≡ y)) → (f : ℕ → τ) → (is : List ℕ) → assoc eq is (map f is) ≡ just (generate f is)
lemma-1 eq f []        = refl
lemma-1 eq f (i ∷ is′) = {!!}

idrange : ℕ → List ℕ
idrange zero = []
idrange (suc n) = zero ∷ (map suc (idrange n))

bff : ({A : Set} → List A → List A) → ({B : Set} → ((x y : B) → Dec (x ≡ y)) → List B → List B → Maybe (List B))
bff get eq s v = let s′ = idrange (length s)
                     g  = fromAscList (zip s′ s)
                     h  = assoc eq (get s′) v
                     h′ = maybe′ (λ jh → just (union jh g)) nothing h
                 in maybe′ (λ jh′ → just (map {!!} s′)) nothing h′
