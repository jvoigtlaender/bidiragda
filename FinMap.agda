module FinMap where

open import Level using () renaming (zero to ℓ₀)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Maybe using (Maybe ; just ; nothing ; maybe′) renaming (setoid to MaybeEq)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Props using (_≟_)
open import Data.Vec using (Vec ; [] ; _∷_ ; _[_]≔_ ; replicate ; tabulate ; foldr ; toList) renaming (lookup to lookupVec ; map to mapV)
open import Data.Vec.Equality using ()
open Data.Vec.Equality.Equality using (_∷-cong_)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Data.List using (List ; [] ; _∷_ ; map ; zip)
open import Data.Product using (_×_ ; _,_)
open import Function using (id ; _∘_ ; flip ; const)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Setoid ; module Setoid)
open import Relation.Binary.Core using (_≡_ ; refl ; _≢_)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; _≗_ ; trans ; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

open import Generic using (just-injective)

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

fromFunc : {A : Set} {n : ℕ} → (Fin n → A) → FinMapMaybe n A
fromFunc = tabulate ∘ _∘_ just

reshape : {n : ℕ} {A : Set} → FinMapMaybe n A → (l : ℕ) → FinMapMaybe l A
reshape m        zero    = []
reshape []       (suc l) = nothing ∷ (reshape [] l)
reshape (x ∷ xs) (suc l) = x ∷ (reshape xs l)

union : {A : Set} {n : ℕ} → FinMapMaybe n A → FinMapMaybe n A → FinMapMaybe n A
union m1 m2 = tabulate (λ f → maybe′ just (lookupM f m2) (lookupM f m1))

restrict : {A : Set} {n : ℕ} → (Fin n → A) → List (Fin n) → FinMapMaybe n A
restrict f is = fromAscList (zip is (map f is))

delete : {A : Set} {n : ℕ} → Fin n → FinMapMaybe n A → FinMapMaybe n A
delete i m = m [ i ]≔ nothing

delete-many : {A : Set} {n m : ℕ} → Vec (Fin n) m → FinMapMaybe n A → FinMapMaybe n A
delete-many = flip (foldr (const _) delete)

lemma-just≢nothing : {A Whatever : Set} {a : A} {ma : Maybe A} → ma ≡ just a → ma ≡ nothing  → Whatever
lemma-just≢nothing refl ()

lemma-insert-same : {n : ℕ} {A : Set} → (m : FinMapMaybe n A) → (f : Fin n) → (a : A) → lookupM f m ≡ just a → m ≡ insert f a m
lemma-insert-same         []       ()      a p
lemma-insert-same {suc n} (x ∷ xs) zero    a p = cong (flip _∷_ xs) p
lemma-insert-same         (x ∷ xs) (suc i) a p = cong (_∷_ x) (lemma-insert-same xs i a p)

lemma-lookupM-empty : {A : Set} {n : ℕ} → (i : Fin n) → lookupM {A} i empty ≡ nothing
lemma-lookupM-empty zero    = refl
lemma-lookupM-empty (suc i) = lemma-lookupM-empty i

lemma-lookupM-insert : {A : Set} {n : ℕ} → (i : Fin n) → (a : A) → (m : FinMapMaybe n A) → lookupM i (insert i a m) ≡ just a
lemma-lookupM-insert zero    a (x ∷ xs) = refl
lemma-lookupM-insert (suc i) a (x ∷ xs) = lemma-lookupM-insert i a xs

lemma-lookupM-insert-other : {A : Set} {n : ℕ} → (i j : Fin n) → (a : A) → (m : FinMapMaybe n A) → i ≢ j → lookupM i m ≡ lookupM i (insert j a m)
lemma-lookupM-insert-other zero    zero    a m        p = contradiction refl p
lemma-lookupM-insert-other zero    (suc j) a (x ∷ xs) p = refl
lemma-lookupM-insert-other (suc i) zero    a (x ∷ xs) p = refl
lemma-lookupM-insert-other (suc i) (suc j) a (x ∷ xs) p = lemma-lookupM-insert-other i j a xs (p ∘ cong suc)

lemma-lookupM-restrict : {A : Set} {n : ℕ} → (i : Fin n) → (f : Fin n → A) → (is : List (Fin n)) → (a : A) → lookupM i (restrict f is) ≡ just a → f i ≡ a
lemma-lookupM-restrict i f []        a p = lemma-just≢nothing p (lemma-lookupM-empty i)
lemma-lookupM-restrict i f (i' ∷ is) a p with i ≟ i'
lemma-lookupM-restrict i f (.i ∷ is) a p | yes refl = just-injective (begin
   just (f i)
     ≡⟨ sym (lemma-lookupM-insert i (f i) (restrict f is)) ⟩
   lookupM i (insert i (f i) (restrict f is))
     ≡⟨ p ⟩
   just a ∎)
lemma-lookupM-restrict i f (i' ∷ is) a p | no i≢i' = lemma-lookupM-restrict i f is a (begin
  lookupM i (restrict f is)
    ≡⟨ lemma-lookupM-insert-other i i' (f i') (restrict f is) i≢i' ⟩
  lookupM i (insert i' (f i') (restrict f is))
    ≡⟨ p ⟩
  just a ∎)

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

lemma-reshape-id : {n : ℕ} {A : Set} → (m : FinMapMaybe n A) → reshape m n ≡ m
lemma-reshape-id []       = refl
lemma-reshape-id (x ∷ xs) = cong (_∷_ x) (lemma-reshape-id xs)

lemma-disjoint-union : {n m : ℕ} {A : Set} → (f : Fin n → A) → (t : Vec (Fin n) m) → union (restrict f (toList t)) (delete-many t (fromFunc f)) ≡ fromFunc f
lemma-disjoint-union {n} {m} f t = lemma-tabulate-∘ (lemma-inner t)
    where lemma-inner : {m : ℕ} → (t : Vec (Fin n) m) → (x : Fin n) → maybe′ just (lookupM x (delete-many t (fromFunc f))) (lookupM x (restrict f (toList t))) ≡ just (f x)
          lemma-inner [] x = begin
            maybe′ just (lookupM x (fromFunc f)) (lookupM x empty)
              ≡⟨ cong (maybe′ just (lookupM x (fromFunc f))) (lemma-lookupM-empty x) ⟩
            lookupM x (fromFunc f)
              ≡⟨ lemma-lookupM-fromFunc f x ⟩
            just (f x) ∎
          lemma-inner (t ∷ ts) x with x ≟ t
          lemma-inner (.x ∷ ts) x | yes refl = cong (maybe′ just (lookupM x (delete-many (x ∷ ts) (fromFunc f)))) (lemma-lookupM-insert x (f x) (restrict f (toList ts)))
          lemma-inner (t ∷ ts) x | no ¬p = begin
            maybe′ just (lookupM x (delete-many (t ∷ ts) (fromFunc f))) (lookupM x (restrict f (toList (t ∷ ts))))
              ≡⟨ cong (maybe′ just (lookupM x (delete-many (t ∷ ts) (fromFunc f)))) (sym (lemma-lookupM-insert-other x t (f t) (restrict f (toList ts)) ¬p)) ⟩
            maybe′ just (lookupM x (delete-many (t ∷ ts) (fromFunc f))) (lookupM x (restrict f (toList ts)))
              ≡⟨ cong (flip (maybe′ just) (lookupM x (restrict f (toList ts)))) (lemma-lookupM-delete (delete-many ts (fromFunc f)) ¬p) ⟩
            maybe′ just (lookupM x (delete-many ts (fromFunc f))) (lookupM x (restrict f (toList ts)))
              ≡⟨ lemma-inner ts x ⟩
            just (f x) ∎
