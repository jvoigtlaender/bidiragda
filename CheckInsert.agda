open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary using (DecSetoid)

module CheckInsert (A : DecSetoid ℓ₀ ℓ₀) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Props using (_≟_)
open import Data.Maybe using (Maybe ; nothing ; just) renaming (setoid to MaybeSetoid ; Eq to MaybeEq)
open import Data.List using (List ; [] ; _∷_)
open import Data.Vec using () renaming (_∷_ to _∷V_)
open import Data.Vec.Equality using () renaming (module Equality to VecEq)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Setoid ; module DecSetoid)
open import Relation.Binary.Core using (refl ; _≡_ ; _≢_)
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; [_] ; trans)

open import FinMap

private
  open module A = DecSetoid A using (Carrier ; _≈_) renaming (_≟_ to deq)

checkInsert : {n : ℕ} → Fin n → Carrier → FinMapMaybe n Carrier → Maybe (FinMapMaybe n Carrier)
checkInsert i b m with lookupM i m
...               | nothing = just (insert i b m)
...               | just c with deq b c
...                         | yes b≈c = just m
...                         | no b≉c  = nothing

data InsertionResult {n : ℕ} (i : Fin n) (x : Carrier) (h : FinMapMaybe n Carrier) : Maybe (FinMapMaybe n Carrier) → Set where
  same : (x' : Carrier) → x ≈ x' → lookupM i h ≡ just x' → InsertionResult i x h (just h)
  new : lookupM i h ≡ nothing → InsertionResult i x h (just (insert i x h))
  wrong : (x' : Carrier) → ¬ (x ≈ x') → lookupM i h ≡ just x' → InsertionResult i x h nothing

insertionresult : {n : ℕ} → (i : Fin n) → (x : Carrier) → (h : FinMapMaybe n Carrier) → InsertionResult i x h (checkInsert i x h)
insertionresult i x h with lookupM i h | inspect (lookupM i) h
insertionresult i x h | just x' | _ with deq x x'
insertionresult i x h | just x' | [ il ] | yes x≈x' = same x' x≈x' il
insertionresult i x h | just x' | [ il ] | no x≉x' = wrong x' x≉x' il
insertionresult i x h | nothing | [ il ] = new il

lemma-checkInsert-same : {n : ℕ} → (i : Fin n) → (x : Carrier) → (m : FinMapMaybe n Carrier) → lookupM i m ≡ just x → checkInsert i x m ≡ just m
lemma-checkInsert-same i x m p with lookupM i m
lemma-checkInsert-same i x m refl | .(just x) with deq x x
lemma-checkInsert-same i x m refl | .(just x) | yes x≈x = refl
lemma-checkInsert-same i x m refl | .(just x) | no x≉x = contradiction A.refl x≉x

lemma-checkInsert-new : {n : ℕ} → (i : Fin n) → (x : Carrier) → (m : FinMapMaybe n Carrier) → lookupM i m ≡ nothing → checkInsert i x m ≡ just (insert i x m)
lemma-checkInsert-new i x m p with lookupM i m
lemma-checkInsert-new i x m refl | .nothing = refl

lemma-checkInsert-wrong : {n : ℕ} → (i : Fin n) → (x : Carrier) → (m : FinMapMaybe n Carrier) → (x' : Carrier) → ¬ (x ≈ x') → lookupM i m ≡ just x' → checkInsert i x m ≡ nothing
lemma-checkInsert-wrong i x m x' d p with lookupM i m
lemma-checkInsert-wrong i x m x' d refl | .(just x') with deq x x'
lemma-checkInsert-wrong i x m x' d refl | .(just x') | yes q = contradiction q d
lemma-checkInsert-wrong i x m x' d refl | .(just x') | no ¬q = refl

lemma-checkInsert-restrict : {n : ℕ} → (f : Fin n → Carrier) → (i : Fin n) → (is : List (Fin n)) → checkInsert i (f i) (restrict f is) ≡ just (restrict f (i ∷ is))
lemma-checkInsert-restrict f i is with checkInsert i (f i) (restrict f is) | insertionresult i (f i) (restrict f is)
lemma-checkInsert-restrict f i is | ._ | same x fi≈x p = cong just (lemma-insert-same _ i (f i) (trans p (cong just (sym (lemma-lookupM-restrict i f is x p)))))
lemma-checkInsert-restrict f i is | ._ | new _ = refl
lemma-checkInsert-restrict f i is | ._ | wrong x fi≉x p = contradiction (Setoid.reflexive A.setoid (lemma-lookupM-restrict i f is x p)) fi≉x

lemma-lookupM-checkInsert : {n : ℕ} → (i j : Fin n) → (x y : Carrier) → (h h' : FinMapMaybe n Carrier) → lookupM i h ≡ just x → checkInsert j y h ≡ just h' → lookupM i h' ≡ just x
lemma-lookupM-checkInsert i j x y h h' pl ph' with checkInsert j y h | insertionresult j y h
lemma-lookupM-checkInsert i j x y h .h pl refl | ._ | same _ _ _ = pl
lemma-lookupM-checkInsert i j x y h h' pl ph'  | ._ | new _ with i ≟ j
lemma-lookupM-checkInsert i .i x y h h' pl ph' | ._ | new pl' | yes refl = contradiction (trans (sym pl) pl') (λ ())
lemma-lookupM-checkInsert i j x y h .(insert j y h) pl refl | ._ | new _ | no i≢j = begin
  lookupM i (insert j y h)
    ≡⟨ lemma-lookupM-insert-other i j y h i≢j ⟩
  lookupM i h
    ≡⟨ pl ⟩
  just x ∎
  where open Relation.Binary.PropositionalEquality.≡-Reasoning

lemma-lookupM-checkInsert i j x y h h' pl () | ._ | wrong _ _ _

lemma-lookupM-checkInsert-other : {n : ℕ} → (i j : Fin n) → i ≢ j → (x : Carrier) → (h h' : FinMapMaybe n Carrier) → checkInsert j x h ≡ just h' → lookupM i h' ≡ lookupM i h
lemma-lookupM-checkInsert-other i j i≢j x h h' ph' with lookupM j h
lemma-lookupM-checkInsert-other i j i≢j x h h' ph' | just y with deq x y
lemma-lookupM-checkInsert-other i j i≢j x h .h refl | just y | yes x≈y = refl
lemma-lookupM-checkInsert-other i j i≢j x h h' () | just y | no x≉y
lemma-lookupM-checkInsert-other i j i≢j x h .(insert j x h) refl | nothing = lemma-lookupM-insert-other i j x h i≢j
