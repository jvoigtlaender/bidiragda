module FinMap where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe ; just ; nothing ; maybe′)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Props using (_≟_)
open import Data.Vec using (Vec ; [] ; _∷_ ; _[_]≔_ ; replicate ; tabulate) renaming (lookup to lookupVec)
open import Data.List using (List ; [] ; _∷_ ; map ; zip)
open import Data.Product using (_×_ ; _,_)
open import Function using (id)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Nullary.Negation using (contradiction ; contraposition)
open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality using (cong ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

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

generate : {A : Set} {n : ℕ} → (Fin n → A) → List (Fin n) → FinMapMaybe n A
generate f is = fromAscList (zip is (map f is))


lemma-insert-same : {τ : Set} {n : ℕ} → (m : FinMapMaybe n τ) → (f : Fin n) → (a : τ) → lookupM f m ≡ just a → m ≡ insert f a m
lemma-insert-same []               ()      a p
lemma-insert-same (.(just a) ∷ xs) zero    a refl = refl
lemma-insert-same (x ∷ xs)         (suc i) a p    = cong (_∷_ x) (lemma-insert-same xs i a p)

lemma-lookupM-empty : {A : Set} {n : ℕ} → (i : Fin n) → lookupM {A} i empty ≡ nothing
lemma-lookupM-empty zero    = refl
lemma-lookupM-empty (suc i) = lemma-lookupM-empty i

lemma-lookupM-insert : {A : Set} {n : ℕ} → (i : Fin n) → (a : A) → (m : FinMapMaybe n A) → lookupM i (insert i a m) ≡ just a
lemma-lookupM-insert zero    _ (_ ∷ _)  = refl
lemma-lookupM-insert (suc i) a (_ ∷ xs) = lemma-lookupM-insert i a xs

lemma-lookupM-insert-other : {A : Set} {n : ℕ} → (i j : Fin n) → (a : A) → (m : FinMapMaybe n A) → ¬(i ≡ j) → lookupM i m ≡ lookupM i (insert j a m)
lemma-lookupM-insert-other zero    zero    a m        p = contradiction refl p
lemma-lookupM-insert-other zero    (suc j) a (x ∷ xs) p = refl
lemma-lookupM-insert-other (suc i) zero    a (x ∷ xs) p = refl
lemma-lookupM-insert-other (suc i) (suc j) a (x ∷ xs) p = lemma-lookupM-insert-other i j a xs (contraposition (cong suc) p)

lemma-from-just : {A : Set} → {x y : A} → _≡_ {_} {Maybe A} (just x) (just y) → x ≡ y
lemma-from-just refl = refl

lemma-lookupM-generate : {A : Set} {n : ℕ} → (i : Fin n) → (f : Fin n → A) → (is : List (Fin n)) → (a : A) → lookupM i (generate f is) ≡ just a → f i ≡ a
lemma-lookupM-generate {A} i f [] a p with begin
  just a
    ≡⟨ sym p ⟩
  lookupM i (generate f [])
    ≡⟨ refl ⟩
  lookupM i empty
    ≡⟨ lemma-lookupM-empty i ⟩
  nothing ∎
lemma-lookupM-generate i f [] a p | ()
lemma-lookupM-generate i f (i' ∷ is) a p with i ≟ i'
lemma-lookupM-generate i f (.i ∷ is) a p | yes refl = lemma-from-just (begin
   just (f i)
     ≡⟨ sym (lemma-lookupM-insert i (f i) (generate f is)) ⟩
   lookupM i (insert i (f i) (generate f is))
     ≡⟨ refl ⟩
   lookupM i (generate f (i ∷ is))
     ≡⟨ p ⟩
   just a ∎)
lemma-lookupM-generate i f (i' ∷ is) a p | no ¬p2 = lemma-lookupM-generate i f is a (begin
  lookupM i (generate f is)
    ≡⟨ lemma-lookupM-insert-other i i' (f i') (generate f is) ¬p2 ⟩
  lookupM i (insert i' (f i') (generate f is))
    ≡⟨ refl ⟩
  lookupM i (generate f (i' ∷ is))
    ≡⟨ p ⟩
  just a ∎)
