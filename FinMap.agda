module FinMap where

open import Level using () renaming (zero to ℓ₀)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Maybe using (Maybe ; just ; nothing ; maybe′)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec using (Vec ; [] ; _∷_ ; _[_]≔_ ; replicate ; tabulate ; foldr ; zip ; toList) renaming (lookup to lookupVec ; map to mapV)
open import Data.Vec.Equality using ()
open import Data.Product using (_×_ ; _,_)
open import Data.List.All as All using (All)
import Data.List.All.Properties as AllP
import Data.List.Any as Any
open import Function using (id ; _∘_ ; flip ; const)
open import Function.Equality using (module Π)
open import Function.Surjection using (module Surjection)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Core using (_≡_ ; refl ; _≢_ ; Decidable)
open import Relation.Binary.PropositionalEquality as P using (cong ; sym ; _≗_ ; trans ; cong₂)
open P.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

open import Generic using (just-injective)

_∈_ : {A : Set} {n : ℕ} → A → Vec A n → Set
_∈_ {A} x xs = Any.Membership._∈_ (P.setoid A) x (toList xs)

_∉_ : {A : Set} {n : ℕ} → A → Vec A n → Set
_∉_ {A} x xs = All (_≢_ x) (toList xs)

data Dec∈ {A : Set} {n : ℕ} (x : A) (xs : Vec A n) : Set where
  yes-∈ : x ∈ xs → Dec∈ x xs
  no-∉ : x ∉ xs → Dec∈ x xs

is-∈ : {A : Set} {n : ℕ} → Decidable (_≡_ {A = A}) → (x : A) → (xs : Vec A n) → Dec∈ x xs
is-∈ eq? x xs with Any.any (eq? x) (toList xs)
...     | yes x∈xs = yes-∈ x∈xs
...     | no  x∉xs = no-∉ (Π._⟨$⟩_ (Surjection.to AllP.¬Any↠All¬) x∉xs)

FinMapMaybe : ℕ → Set → Set
FinMapMaybe n A = Vec (Maybe A) n

lookupM : {A : Set} {n : ℕ} → Fin n → FinMapMaybe n A → Maybe A
lookupM = lookupVec

insert : {A : Set} {n : ℕ} → Fin n → A → FinMapMaybe n A → FinMapMaybe n A
insert f a m = m [ f ]≔ (just a)

empty : {A : Set} {n : ℕ} → FinMapMaybe n A
empty = replicate nothing

fromAscList : {A : Set} {n m : ℕ} → Vec (Fin n × A) m → FinMapMaybe n A
fromAscList []             = empty
fromAscList ((f , a) ∷ xs) = insert f a (fromAscList xs)

fromFunc : {A : Set} {n : ℕ} → (Fin n → A) → FinMapMaybe n A
fromFunc = tabulate ∘ _∘_ Maybe.just

reshape : {n : ℕ} {A : Set} → FinMapMaybe n A → (l : ℕ) → FinMapMaybe l A
reshape m        zero    = []
reshape []       (suc l) = nothing ∷ (reshape [] l)
reshape (x ∷ xs) (suc l) = x ∷ (reshape xs l)

union : {A : Set} {n : ℕ} → FinMapMaybe n A → FinMapMaybe n A → FinMapMaybe n A
union m1 m2 = tabulate (λ f → maybe′ just (lookupM f m2) (lookupM f m1))

restrict : {A : Set} {n m : ℕ} → (Fin n → A) → Vec (Fin n) m → FinMapMaybe n A
restrict f is = fromAscList (zip is (mapV f is))

delete : {A : Set} {n : ℕ} → Fin n → FinMapMaybe n A → FinMapMaybe n A
delete i m = m [ i ]≔ nothing

delete-many : {A : Set} {n m : ℕ} → Vec (Fin n) m → FinMapMaybe n A → FinMapMaybe n A
delete-many = flip (foldr (const _) delete)

lemma-insert-same : {n : ℕ} {A : Set} → (m : FinMapMaybe n A) → (f : Fin n) → {a : A} → lookupM f m ≡ just a → m ≡ insert f a m
lemma-insert-same         []       ()      p
lemma-insert-same {suc n} (x ∷ xs) zero    p = cong (flip _∷_ xs) p
lemma-insert-same         (x ∷ xs) (suc i) p = cong (_∷_ x) (lemma-insert-same xs i p)

lemma-lookupM-empty : {A : Set} {n : ℕ} → (i : Fin n) → lookupM {A} i empty ≡ nothing
lemma-lookupM-empty zero    = refl
lemma-lookupM-empty (suc i) = lemma-lookupM-empty i

lemma-lookupM-insert : {A : Set} {n : ℕ} → (i : Fin n) → (a : A) → (m : FinMapMaybe n A) → lookupM i (insert i a m) ≡ just a
lemma-lookupM-insert zero    a (x ∷ xs) = refl
lemma-lookupM-insert (suc i) a (x ∷ xs) = lemma-lookupM-insert i a xs

lemma-lookupM-insert-other : {A : Set} {n : ℕ} → (i j : Fin n) → (a : A) → (m : FinMapMaybe n A) → i ≢ j → lookupM i (insert j a m) ≡ lookupM i m
lemma-lookupM-insert-other zero    zero    a m        p = contradiction refl p
lemma-lookupM-insert-other zero    (suc j) a (x ∷ xs) p = refl
lemma-lookupM-insert-other (suc i) zero    a (x ∷ xs) p = refl
lemma-lookupM-insert-other (suc i) (suc j) a (x ∷ xs) p = lemma-lookupM-insert-other i j a xs (p ∘ cong suc)

lemma-lookupM-restrict : {A : Set} {n m : ℕ} → (i : Fin n) → (f : Fin n → A) → (is : Vec (Fin n) m) → {a : A} → lookupM i (restrict f is) ≡ just a → f i ≡ a
lemma-lookupM-restrict i f []            p = contradiction (trans (sym p) (lemma-lookupM-empty i)) (λ ())
lemma-lookupM-restrict i f (i' ∷ is)     p with i ≟ i'
lemma-lookupM-restrict i f (.i ∷ is) {a} p | yes refl = just-injective (begin
   just (f i)
     ≡⟨ sym (lemma-lookupM-insert i (f i) (restrict f is)) ⟩
   lookupM i (insert i (f i) (restrict f is))
     ≡⟨ p ⟩
   just a ∎)
lemma-lookupM-restrict i f (i' ∷ is) {a} p | no i≢i' = lemma-lookupM-restrict i f is (begin
  lookupM i (restrict f is)
    ≡⟨ sym (lemma-lookupM-insert-other i i' (f i') (restrict f is) i≢i') ⟩
  lookupM i (insert i' (f i') (restrict f is))
    ≡⟨ p ⟩
  just a ∎)
lemma-lookupM-restrict-∈ : {A : Set} {n m : ℕ} → (i : Fin n) → (f : Fin n → A) → (js : Vec (Fin n) m) → i ∈ js → lookupM i (restrict f js) ≡ just (f i)
lemma-lookupM-restrict-∈ i f [] ()
lemma-lookupM-restrict-∈ i f (j ∷ js)  p             with i ≟ j
lemma-lookupM-restrict-∈ i f (.i ∷ js) p             | yes refl = lemma-lookupM-insert i (f i) (restrict f js)
lemma-lookupM-restrict-∈ i f (j ∷ js) (Any.here i≡j) | no i≢j = contradiction i≡j i≢j
lemma-lookupM-restrict-∈ i f (j ∷ js) (Any.there p)  | no i≢j =
  trans (lemma-lookupM-insert-other i j (f j) (restrict f js) i≢j)
        (lemma-lookupM-restrict-∈ i f js p)

lemma-lookupM-restrict-∉ : {A : Set} {n m : ℕ} → (i : Fin n) → (f : Fin n → A) → (js : Vec (Fin n) m) → i ∉ js → lookupM i (restrict f js) ≡ nothing
lemma-lookupM-restrict-∉ i f []       i∉[]  = lemma-lookupM-empty i
lemma-lookupM-restrict-∉ i f (j ∷ js) i∉jjs =
  trans (lemma-lookupM-insert-other i j (f j) (restrict f js) (All.head i∉jjs))
        (lemma-lookupM-restrict-∉ i f js (All.tail i∉jjs))

lemma-tabulate-∘ : {n : ℕ} {A : Set} → {f g : Fin n → A} → f ≗ g → tabulate f ≡ tabulate g
lemma-tabulate-∘ {zero}  {_} {f} {g} f≗g = refl
lemma-tabulate-∘ {suc n} {_} {f} {g} f≗g = cong₂ _∷_ (f≗g zero) (lemma-tabulate-∘ (f≗g ∘ suc))

lemma-lookupM-fromFunc : {n : ℕ} {A : Set} → (f : Fin n → A) → flip lookupM (fromFunc f) ≗ Maybe.just ∘ f
lemma-lookupM-fromFunc f zero = refl
lemma-lookupM-fromFunc f (suc i) = lemma-lookupM-fromFunc (f ∘ suc) i

lemma-lookupM-delete : {n : ℕ} {A : Set} {i j : Fin n} → (f : FinMapMaybe n A) → i ≢ j → lookupM i (delete j f) ≡ lookupM i f
lemma-lookupM-delete {i = zero}  {j = zero}  (_ ∷ _)  p = contradiction refl p
lemma-lookupM-delete {i = zero}  {j = suc j} (_ ∷ _)  p = refl
lemma-lookupM-delete {i = suc i} {j = zero}  (x ∷ xs) p = refl
lemma-lookupM-delete {i = suc i} {j = suc j} (x ∷ xs) p = lemma-lookupM-delete xs (p ∘ cong suc)

lemma-lookupM-delete-many : {n m : ℕ} {A : Set} (h : FinMapMaybe n A) → (i : Fin n) → (js : Vec (Fin n) m) → i ∉ js → lookupM i (delete-many js h) ≡ lookupM i h
lemma-lookupM-delete-many {n} h i []       i∉[]  = refl
lemma-lookupM-delete-many {n} h i (j ∷ js) i∉jjs =
  trans (lemma-lookupM-delete (delete-many js h) (All.head i∉jjs))
        (lemma-lookupM-delete-many h i js (All.tail i∉jjs))

lemma-reshape-id : {n : ℕ} {A : Set} → (m : FinMapMaybe n A) → reshape m n ≡ m
lemma-reshape-id []       = refl
lemma-reshape-id (x ∷ xs) = cong (_∷_ x) (lemma-reshape-id xs)

lemma-disjoint-union : {n m : ℕ} {A : Set} → (f : Fin n → A) → (t : Vec (Fin n) m) → union (restrict f t) (delete-many t (fromFunc f)) ≡ fromFunc f
lemma-disjoint-union {n} f t = lemma-tabulate-∘ inner
  where inner : (x : Fin n) → maybe′ just (lookupM x (delete-many t (fromFunc f))) (lookupM x (restrict f t)) ≡ just (f x)
        inner x with is-∈ _≟_ x t
        inner x | yes-∈ x∈t = cong (maybe′ just (lookupM x (delete-many t (fromFunc f)))) (lemma-lookupM-restrict-∈ x f t x∈t)
        inner x | no-∉ x∉t = begin
          maybe′ just (lookupM x (delete-many t (fromFunc f))) (lookupM x (restrict f t))
            ≡⟨ cong₂ (maybe′ just) (lemma-lookupM-delete-many (fromFunc f) x t x∉t) (lemma-lookupM-restrict-∉ x f t x∉t) ⟩
          maybe′ just (lookupM x (fromFunc f)) nothing
            ≡⟨ lemma-lookupM-fromFunc f x ⟩
          just (f x) ∎
