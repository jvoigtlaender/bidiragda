module Bidir where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe ; nothing ; just ; maybe′)
open import Data.List using (List ; [] ; _∷_ ; map ; length)
open import Data.Vec using (toList ; fromList ; tabulate) renaming (lookup to lookupVec)
open import Function using (id ; _∘_ ; flip)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; Reveal_is_)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

open import FinMap

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
_>>=_ = flip (flip maybe′ nothing)

fmap : {A B : Set} → (A → B) → Maybe A → Maybe B
fmap f = maybe′ (λ a → just (f a)) nothing

EqInst : Set → Set
EqInst A = (x y : A) → Dec (x ≡ y)

checkInsert : {A : Set} {n : ℕ} → EqInst A → Fin n → A → FinMapMaybe n A → Maybe (FinMapMaybe n A)
checkInsert eq i b m with lookupM i m
checkInsert eq i b m | just c with eq b c
checkInsert eq i b m | just .b | yes refl = just m
checkInsert eq i b m | just c  | no ¬p    = nothing
checkInsert eq i b m | nothing = just (insert i b m)
assoc : {A : Set} {n : ℕ} → EqInst A → List (Fin n) → List A → Maybe (FinMapMaybe n A)
assoc _  []       []       = just empty
assoc eq (i ∷ is) (b ∷ bs) = (assoc eq is bs) >>= (checkInsert eq i b)
assoc _  _        _        = nothing

lemma-checkInsert-generate : {τ : Set} {n : ℕ} → (eq : EqInst τ) → (f : Fin n → τ) → (i : Fin n) → (is : List (Fin n)) → checkInsert eq i (f i) (generate f is) ≡ just (generate f (i ∷ is))
lemma-checkInsert-generate eq f i is with lookupM i (generate f is) | inspect (lookupM i) (generate f is)
lemma-checkInsert-generate eq f i is | nothing     | _ = refl
lemma-checkInsert-generate eq f i is | just x      | Reveal_is_.[_] prf with lemma-lookupM-generate i f is x prf
lemma-checkInsert-generate eq f i is | just .(f i) | Reveal_is_.[_] prf | refl with eq (f i) (f i)
lemma-checkInsert-generate eq f i is | just .(f i) | Reveal_is_.[_] prf | refl | yes refl = cong just (lemma-insert-same (generate f is) i (f i) prf)
lemma-checkInsert-generate eq f i is | just .(f i) | Reveal_is_.[_] prf | refl | no  ¬p   = contradiction refl ¬p

lemma-1 : {τ : Set} {n : ℕ} → (eq : EqInst τ) → (f : Fin n → τ) → (is : List (Fin n)) → assoc eq is (map f is) ≡ just (generate f is)
lemma-1 eq f []        = refl
lemma-1 eq f (i ∷ is′) = begin
  (assoc eq (i ∷ is′) (map f (i ∷ is′)))
    ≡⟨ refl ⟩
  (assoc eq is′ (map f is′) >>= checkInsert eq i (f i))
    ≡⟨ cong (λ m → m >>= checkInsert eq i (f i)) (lemma-1 eq f is′) ⟩
  (just (generate f is′) >>= (checkInsert eq i (f i)))
    ≡⟨ refl ⟩
  (checkInsert eq i (f i) (generate f is′))
    ≡⟨ lemma-checkInsert-generate eq f i is′ ⟩
  just (generate f (i ∷ is′)) ∎

lemma-lookupM-assoc : {A : Set} {n : ℕ} → (eq : EqInst A) → (i : Fin n) → (is : List (Fin n)) → (x : A) → (xs : List A) → (h : FinMapMaybe n A) → assoc eq (i ∷ is) (x ∷ xs) ≡ just h → lookupM i h ≡ just x
lemma-lookupM-assoc eq i is x xs h    p with assoc eq is xs
lemma-lookupM-assoc eq i is x xs h    ()   | nothing
lemma-lookupM-assoc eq i is x xs h    p    | just h' with lookupM i h' | inspect (lookupM i) h'
lemma-lookupM-assoc eq i is x xs .(insert i x h') refl | just h' | nothing | _ = lemma-lookupM-insert i x h'
lemma-lookupM-assoc eq i is x xs h    p    | just h'   | just y  | _ with eq x y
lemma-lookupM-assoc eq i is x xs h    ()   | just h'   | just y  | _ | no ¬prf
lemma-lookupM-assoc eq i is x xs h    p    | just h'   | just .x | Reveal_is_.[_] p' | yes refl = begin
  lookupM i h
    ≡⟨ cong (lookupM i) (lemma-from-just (sym p)) ⟩
  lookupM i h'
    ≡⟨ p' ⟩
  just x ∎

lemma-2 : {τ : Set} {n : ℕ} → (eq : EqInst τ) → (is : List (Fin n)) → (v : List τ) → (h : FinMapMaybe n τ) → assoc eq is v ≡ just h → map (flip lookupM h) is ≡ map just v
lemma-2 eq []       []       h p = refl
lemma-2 eq []       (x ∷ xs) h ()
lemma-2 eq (x ∷ xs) []       h ()
lemma-2 eq (i ∷ is) (x ∷ xs) h p with assoc eq is xs | inspect (assoc eq is) xs
lemma-2 eq (i ∷ is) (x ∷ xs) h () | nothing | _
lemma-2 eq (i ∷ is) (x ∷ xs) h p | just h' | Reveal_is_.[_] ir = begin
  map (flip lookupM h) (i ∷ is)
    ≡⟨ refl ⟩
  lookup i h ∷ map (flip lookupM h) is
    ≡⟨ cong (flip _∷_ (map (flip lookup h) is)) (lemma-lookupM-assoc eq i is x xs h (begin
      assoc eq (i ∷ is) (x ∷ xs)
        ≡⟨ cong (flip _>>=_ (checkInsert eq i x)) ir ⟩
      checkInsert eq i x h'
        ≡⟨ p ⟩
      just h ∎) ) ⟩
  just x ∷ map (flip lookupM h) is
    ≡⟨  cong (_∷_ (just x)) {!!} ⟩
  just x ∷ map (flip lookupM h') is
    ≡⟨ cong (_∷_ (just x)) (lemma-2 eq is xs h' ir) ⟩
  just x ∷ map just xs
    ≡⟨ refl ⟩
  map just (x ∷ xs) ∎

idrange : (n : ℕ) → List (Fin n)
idrange n = toList (tabulate id)

bff : ({A : Set} → List A → List A) → ({B : Set} → EqInst B → List B → List B → Maybe (List B))
bff get eq s v = let s′ = idrange (length s)
                     g  = fromFunc (λ f → lookupVec f (fromList s))
                     h  = assoc eq (get s′) v
                     h′ = fmap (flip union g) h
                 in fmap (flip map s′ ∘ flip lookup) h′

postulate
  free-theorem-list-list : {β γ : Set} → (get : {α : Set} → List α → List α) → (f : β → γ) → (l : List β) → get (map f l) ≡ map f (get l)

theorem-1 : (get : {α : Set} → List α → List α) → {τ : Set} → (eq : EqInst τ) → (s : List τ) → bff get eq s (get s) ≡ just s
theorem-1 get eq s = {!!}
