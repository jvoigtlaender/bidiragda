module Bidir where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

equal? : ℕ -> ℕ -> Bool
equal? zero    zero    = true
equal? (suc n) (suc m) = equal? n m
equal? _       _       = false

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

maybeToBool : {A : Set} → Maybe A → Bool
maybeToBool nothing  = false
maybeToBool (just _) = true

maybe′ : {A B : Set} → (A → Maybe B) → Maybe B → Maybe A → Maybe B
maybe′ y _ (just a) = y a
maybe′ _ n nothing  = n

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
_++_ []        ys = ys
_++_ (x ∷ xs) ys = x ∷ (xs ++ ys)

map : {A B : Set} → (A → B) → List A → List B
map f []        = []
map f (x ∷ xs) = f x ∷ map f xs

zip : {A B : Set} → List A → List B → List (A × B)
zip (a ∷ as) (b ∷ bs) = (a , b) ∷ zip as bs
zip _         _         = []

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x

module NatMap where

  NatMap : Set → Set
  NatMap A = List (ℕ × A)

  lookup : {A : Set} → ℕ → NatMap A → Maybe A
  lookup n []       = nothing
  lookup n ((m , a) ∷ xs) with equal? n m
  lookup n ((m , a) ∷ xs) | true = just a
  lookup n ((m , a) ∷ xs) | false        = lookup n xs

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

checkInsert : {A : Set} → (A → A → Bool) → ℕ → A → NatMap A → Maybe (NatMap A)
checkInsert eq i b m with lookup i m
checkInsert eq i b m | just c with eq b c
checkInsert eq i b m | just c | true = just m
checkInsert eq i b m | just c | false = nothing
checkInsert eq i b m | nothing = just (insert i b m)

assoc : {A : Set} → (A → A → Bool) → List ℕ → List A → Maybe (NatMap A)
assoc _  []       []       = just empty
assoc eq (i ∷ is) (b ∷ bs) = maybe′ (checkInsert eq i b) nothing (assoc eq is bs)
assoc _  _        _        = nothing

--data Equal? where
--  same ...
--  different ...

generate : {A : Set} → (ℕ → A) → List ℕ → NatMap A
generate f []       = empty
generate f (n ∷ ns) = insert n (f n) (generate f ns)

-- this lemma is probably wrong, because two different NatMaps may represent the same semantic value.
lemma-1 : {τ : Set} → (eq : τ → τ → Bool) → (f : ℕ → τ) → (is : List ℕ) → assoc eq is (map f is) == just (generate f is)
lemma-1 eq f []        = refl
lemma-1 eq f (i ∷ is′) = {!!}
