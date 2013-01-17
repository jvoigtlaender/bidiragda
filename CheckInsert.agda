open import Relation.Binary.Core using (Decidable ; _≡_)

module CheckInsert (Carrier : Set) (deq : Decidable {A = Carrier} _≡_) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Props using (_≟_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.List using (List ; [] ; _∷_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Core using (refl ; _≢_)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; [_] ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

open import FinMap

checkInsert : {n : ℕ} → Fin n → Carrier → FinMapMaybe n Carrier → Maybe (FinMapMaybe n Carrier)
checkInsert i b m with lookupM i m
...               | nothing = just (insert i b m)
...               | just c with deq b c
...                         | yes b≡c = just m
...                         | no b≢c  = nothing

data InsertionResult {n : ℕ} (i : Fin n) (x : Carrier) (h : FinMapMaybe n Carrier) : Maybe (FinMapMaybe n Carrier) → Set where
  insert-same : lookupM i h ≡ just x → InsertionResult i x h (just h)
  insert-new : lookupM i h ≡ nothing → InsertionResult i x h (just (insert i x h))
  insert-wrong : (x' : Carrier) → x ≢ x' → lookupM i h ≡ just x' → InsertionResult i x h nothing

insertionresult : {n : ℕ} → (i : Fin n) → (x : Carrier) → (h : FinMapMaybe n Carrier) → InsertionResult i x h (checkInsert i x h)
insertionresult i x h with lookupM i h | inspect (lookupM i) h
insertionresult i x h | just x' | _ with deq x x'
insertionresult i x h | just .x | [ il ] | yes refl = insert-same il
insertionresult i x h | just x' | [ il ] | no x≢x' = insert-wrong x' x≢x' il
insertionresult i x h | nothing | [ il ] = insert-new il

lemma-checkInsert-same : {n : ℕ} → (i : Fin n) → (x : Carrier) → (m : FinMapMaybe n Carrier) → lookupM i m ≡ just x → checkInsert i x m ≡ just m
lemma-checkInsert-same i x m p with lookupM i m
lemma-checkInsert-same i x m refl | .(just x) with deq x x
lemma-checkInsert-same i x m refl | .(just x) | yes refl = refl
lemma-checkInsert-same i x m refl | .(just x) | no x≢x = contradiction refl x≢x

lemma-checkInsert-new : {n : ℕ} → (i : Fin n) → (x : Carrier) → (m : FinMapMaybe n Carrier) → lookupM i m ≡ nothing → checkInsert i x m ≡ just (insert i x m)
lemma-checkInsert-new i x m p with lookupM i m
lemma-checkInsert-new i x m refl | .nothing = refl

lemma-checkInsert-wrong : {n : ℕ} → (i : Fin n) → (x : Carrier) → (m : FinMapMaybe n Carrier) → (x' : Carrier) → x ≢ x' → lookupM i m ≡ just x' → checkInsert i x m ≡ nothing
lemma-checkInsert-wrong i x m x' d p with lookupM i m
lemma-checkInsert-wrong i x m x' d refl | .(just x') with deq x x'
lemma-checkInsert-wrong i x m x' d refl | .(just x') | yes q = contradiction q d
lemma-checkInsert-wrong i x m x' d refl | .(just x') | no ¬q = refl

lemma-checkInsert-restrict : {n : ℕ} → (f : Fin n → Carrier) → (i : Fin n) → (is : List (Fin n)) → checkInsert i (f i) (restrict f is) ≡ just (restrict f (i ∷ is))
lemma-checkInsert-restrict f i is with checkInsert i (f i) (restrict f is) | insertionresult i (f i) (restrict f is)
lemma-checkInsert-restrict f i is | ._ | insert-same p = cong just (lemma-insert-same _ i (f i) p)
lemma-checkInsert-restrict f i is | ._ | insert-new _ = refl
lemma-checkInsert-restrict f i is | ._ | insert-wrong x fi≢x p = contradiction (lemma-lookupM-restrict i f is x p) fi≢x

lemma-lookupM-checkInsert : {n : ℕ} → (i j : Fin n) → (x y : Carrier) → (h h' : FinMapMaybe n Carrier) → lookupM i h ≡ just x → checkInsert j y h ≡ just h' → lookupM i h' ≡ just x
lemma-lookupM-checkInsert i j x y h h' pl ph' with lookupM j h | inspect (lookupM j) h
lemma-lookupM-checkInsert i j x y h .(insert j y h) pl refl | nothing | pl' with i ≟ j
lemma-lookupM-checkInsert i .i x y h .(insert i y h) pl refl | nothing | [ pl' ] | yes refl = lemma-just≢nothing pl pl'
lemma-lookupM-checkInsert i j x y h .(insert j y h) pl refl | nothing | pl' | no ¬p = begin
  lookupM i (insert j y h)
    ≡⟨ sym (lemma-lookupM-insert-other i j y h ¬p) ⟩
  lookupM i h
    ≡⟨ pl ⟩
  just x ∎
lemma-lookupM-checkInsert i j x y h h' pl ph' | just z | pl' with deq y z
lemma-lookupM-checkInsert i j x y h .h pl refl | just .y | pl' | yes refl = pl
lemma-lookupM-checkInsert i j x y h h' pl () | just z | pl' | no ¬p

lemma-lookupM-checkInsert-other : {n : ℕ} → (i j : Fin n) → i ≢ j → (x : Carrier) → (h h' : FinMapMaybe n Carrier) → checkInsert j x h ≡ just h' → lookupM i h ≡ lookupM i h'
lemma-lookupM-checkInsert-other i j i≢j x h h' ph' with lookupM j h
lemma-lookupM-checkInsert-other i j i≢j x h h' ph' | just y with deq x y
lemma-lookupM-checkInsert-other i j i≢j x h .h refl | just .x | yes refl = refl
lemma-lookupM-checkInsert-other i j i≢j x h h' () | just y | no x≢y
lemma-lookupM-checkInsert-other i j i≢j x h .(insert j x h) refl | nothing = lemma-lookupM-insert-other i j x h i≢j
