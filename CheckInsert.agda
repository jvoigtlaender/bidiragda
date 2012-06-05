module CheckInsert where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Props using (_≟_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.List using (List ; [] ; _∷_)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; Reveal_is_ ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

open import FinMap

EqInst : Set → Set
EqInst A = (x y : A) → Dec (x ≡ y)

checkInsert : {A : Set} {n : ℕ} → EqInst A → Fin n → A → FinMapMaybe n A → Maybe (FinMapMaybe n A)
checkInsert eq i b m with lookupM i m
checkInsert eq i b m | just c with eq b c
checkInsert eq i b m | just .b | yes refl = just m
checkInsert eq i b m | just c  | no ¬p    = nothing
checkInsert eq i b m | nothing = just (insert i b m)

record checkInsertProof {A : Set} {n : ℕ} (eq : EqInst A) (i : Fin n) (x : A) (m : FinMapMaybe n A) (P : Set) : Set where
  field
     same : lookupM i m ≡ just x → P
     new : lookupM i m ≡ nothing → P
     wrong : (x' : A) → ¬(x ≡ x') → lookupM i m ≡ just x'  → P

apply-checkInsertProof : {A P : Set} {n : ℕ} → (eq : EqInst A) → (i : Fin n) → (x : A) → (m : FinMapMaybe n A) → checkInsertProof eq i x m P → P
apply-checkInsertProof eq i x m rp with lookupM i m | inspect (lookupM i) m
apply-checkInsertProof eq i x m rp | just x' | il with eq x x'
apply-checkInsertProof eq i x m rp | just .x | Reveal_is_.[_] il | yes refl = checkInsertProof.same rp il
apply-checkInsertProof eq i x m rp | just x' | Reveal_is_.[_] il | no x≢x' = checkInsertProof.wrong rp x' x≢x' il
apply-checkInsertProof eq i x m rp | nothing | Reveal_is_.[_] il = checkInsertProof.new rp il

lemma-checkInsert-same : {A : Set} {n : ℕ} → (eq : EqInst A) → (i : Fin n) → (x : A) → (m : FinMapMaybe n A) → lookupM i m ≡ just x → checkInsert eq i x m ≡ just m
lemma-checkInsert-same eq i x m p with lookupM i m
lemma-checkInsert-same eq i x m refl | .(just x) with eq x x
lemma-checkInsert-same eq i x m refl | .(just x) | yes refl = refl
lemma-checkInsert-same eq i x m refl | .(just x) | no x≢x = contradiction refl x≢x

lemma-checkInsert-new : {A : Set} {n : ℕ} → (eq : EqInst A) → (i : Fin n) → (x : A) → (m : FinMapMaybe n A) → lookupM i m ≡ nothing → checkInsert eq i x m ≡ just (insert i x m)
lemma-checkInsert-new eq i x m p with lookupM i m
lemma-checkInsert-new eq i x m refl | .nothing = refl

lemma-checkInsert-wrong : {A : Set} {n : ℕ} → (eq : EqInst A) → (i : Fin n) → (x : A) → (m : FinMapMaybe n A) → (x' : A) → ¬(x ≡ x') → lookupM i m ≡ just x' → checkInsert eq i x m ≡ nothing
lemma-checkInsert-wrong eq i x m x' d p with lookupM i m
lemma-checkInsert-wrong eq i x m x' d refl | .(just x') with eq x x'
lemma-checkInsert-wrong eq i x m x' d refl | .(just x') | yes q = contradiction q d
lemma-checkInsert-wrong eq i x m x' d refl | .(just x') | no ¬q = refl

record checkInsertEqualProof {A : Set} {n : ℕ} (eq : EqInst A) (i : Fin n) (x : A) (m : FinMapMaybe n A) (e : Maybe (FinMapMaybe n A)) : Set where
  field
     same : lookupM i m ≡ just x → just m ≡ e
     new : lookupM i m ≡ nothing → just (insert i x m) ≡ e
     wrong : (x' : A) → ¬(x ≡ x') → lookupM i m ≡ just x' → nothing ≡ e

lift-checkInsertProof : {A : Set} {n : ℕ} {eq : EqInst A} {i : Fin n} {x : A} {m : FinMapMaybe n A} {e : Maybe (FinMapMaybe n A)} → checkInsertEqualProof eq i x m e → checkInsertProof eq i x m (checkInsert eq i x m ≡ e)
lift-checkInsertProof {_} {_} {eq} {i} {x} {m} o = record
  { same  = λ p → trans (lemma-checkInsert-same eq i x m p) (checkInsertEqualProof.same o p)
  ; new   = λ p → trans (lemma-checkInsert-new eq i x m p) (checkInsertEqualProof.new o p)
  ; wrong = λ x' q p → trans (lemma-checkInsert-wrong eq i x m x' q p) (checkInsertEqualProof.wrong o x' q p)
  }

lemma-checkInsert-restrict : {τ : Set} {n : ℕ} → (eq : EqInst τ) → (f : Fin n → τ) → (i : Fin n) → (is : List (Fin n)) → checkInsert eq i (f i) (restrict f is) ≡ just (restrict f (i ∷ is))
lemma-checkInsert-restrict {τ} eq f i is = apply-checkInsertProof eq i (f i) (restrict f is) (lift-checkInsertProof record
  { same  = λ lookupM≡justx → cong just (lemma-insert-same (restrict f is) i (f i) lookupM≡justx)
  ; new   = λ lookupM≡nothing → refl
  ; wrong = λ x' x≢x' lookupM≡justx' → contradiction (lemma-lookupM-restrict i f is x' lookupM≡justx') x≢x'
  })

lemma-lookupM-checkInsert : {A : Set} {n : ℕ} → (eq : EqInst A) → (i j : Fin n) → (x y : A) → (h h' : FinMapMaybe n A) → lookupM i h ≡ just x → checkInsert eq j y h ≡ just h' → lookupM i h' ≡ just x
lemma-lookupM-checkInsert eq i j x y h h' pl ph' with lookupM j h | inspect (lookupM j) h
lemma-lookupM-checkInsert eq i j x y h .(insert j y h) pl refl | nothing | pl' with i ≟ j
lemma-lookupM-checkInsert eq i .i x y h .(insert i y h) pl refl | nothing | Reveal_is_.[_] pl' | yes refl with begin just x ≡⟨ sym pl ⟩ lookupM i h ≡⟨ pl' ⟩ nothing ∎
... | ()
lemma-lookupM-checkInsert eq i j x y h .(insert j y h) pl refl | nothing | pl' | no ¬p = begin
  lookupM i (insert j y h)
    ≡⟨ sym (lemma-lookupM-insert-other i j y h ¬p) ⟩
  lookupM i h
    ≡⟨ pl ⟩
  just x ∎
lemma-lookupM-checkInsert eq i j x y h h' pl ph' | just z | pl' with eq y z
lemma-lookupM-checkInsert eq i j x y h h' pl ph' | just .y | pl' | yes refl = begin
  lookupM i h'
    ≡⟨ cong (lookupM i) (lemma-from-just (sym ph')) ⟩
  lookupM i h
    ≡⟨ pl ⟩
  just x ∎
lemma-lookupM-checkInsert eq i j x y h h' pl () | just z | pl' | no ¬p
