module Bidir where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe ; nothing ; just ; maybe′)
open import Data.List using (List ; [] ; _∷_ ; map ; length)
open import Data.List.Properties using (map-cong) renaming (map-compose to map-∘)
open import Data.Vec using (toList ; fromList ; tabulate) renaming (lookup to lookupVec ; _∷_ to _∷V_)
open import Data.Vec.Properties using (tabulate-∘ ; lookup∘tabulate)
open import Function using (id ; _∘_ ; flip)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; Reveal_is_ ; _≗_)
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

lemma-checkInsert-restrict : {τ : Set} {n : ℕ} → (eq : EqInst τ) → (f : Fin n → τ) → (i : Fin n) → (is : List (Fin n)) → checkInsert eq i (f i) (restrict f is) ≡ just (restrict f (i ∷ is))
lemma-checkInsert-restrict eq f i is with lookupM i (restrict f is) | inspect (lookupM i) (restrict f is)
lemma-checkInsert-restrict eq f i is | nothing     | _ = refl
lemma-checkInsert-restrict eq f i is | just x      | Reveal_is_.[_] prf with lemma-lookupM-restrict i f is x prf
lemma-checkInsert-restrict eq f i is | just .(f i) | Reveal_is_.[_] prf | refl with eq (f i) (f i)
lemma-checkInsert-restrict eq f i is | just .(f i) | Reveal_is_.[_] prf | refl | yes refl = cong just (lemma-insert-same (restrict f is) i (f i) prf)
lemma-checkInsert-restrict eq f i is | just .(f i) | Reveal_is_.[_] prf | refl | no  ¬p   = contradiction refl ¬p

lemma-1 : {τ : Set} {n : ℕ} → (eq : EqInst τ) → (f : Fin n → τ) → (is : List (Fin n)) → assoc eq is (map f is) ≡ just (restrict f is)
lemma-1 eq f []        = refl
lemma-1 eq f (i ∷ is′) = begin
  assoc eq (i ∷ is′) (map f (i ∷ is′))
    ≡⟨ refl ⟩
  assoc eq is′ (map f is′) >>= checkInsert eq i (f i)
    ≡⟨ cong (λ m → m >>= checkInsert eq i (f i)) (lemma-1 eq f is′) ⟩
  just (restrict f is′) >>= (checkInsert eq i (f i))
    ≡⟨ refl ⟩
  checkInsert eq i (f i) (restrict f is′)
    ≡⟨ lemma-checkInsert-restrict eq f i is′ ⟩
  just (restrict f (i ∷ is′)) ∎

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

enumerate : {A : Set} → (l : List A) → List (Fin (length l))
enumerate l = toList (tabulate id)

denumerate : {A : Set} (l : List A) → Fin (length l) → A
denumerate l = flip lookupVec (fromList l)

bff : ({A : Set} → List A → List A) → ({B : Set} → EqInst B → List B → List B → Maybe (List B))
bff get eq s v = let s′ = enumerate s
                     g  = fromFunc (denumerate s)
                     h  = assoc eq (get s′) v
                     h′ = fmap (flip union g) h
                 in fmap (flip map s′ ∘ flip lookup) h′

postulate
  free-theorem-list-list : {β γ : Set} → (get : {α : Set} → List α → List α) → (f : β → γ) → get ∘ map f ≗ map f ∘ get

toList-map-commutes : {A B : Set} {n : ℕ} → (f : A → B) → (v : Data.Vec.Vec A n) → (toList (Data.Vec.map f v)) ≡ map f (toList v)
toList-map-commutes f Data.Vec.[] = refl
toList-map-commutes f (x ∷V xs) = cong (_∷_ (f x)) (toList-map-commutes f xs)

lemma-map-denumerate-enumerate : {A : Set} → (as : List A) → map (denumerate as) (enumerate as) ≡ as
lemma-map-denumerate-enumerate [] = refl
lemma-map-denumerate-enumerate (a ∷ as) = cong (_∷_ a) (begin
  map (flip lookupVec (a ∷V (fromList as))) (toList (tabulate Fin.suc))
    ≡⟨ cong (map (flip lookupVec (a ∷V (fromList as))) ∘ toList) (tabulate-∘ Fin.suc id) ⟩
  map (flip lookupVec (a ∷V (fromList as))) (toList (Data.Vec.map Fin.suc (tabulate id)))
    ≡⟨ cong (map (flip lookupVec (a ∷V fromList as))) (toList-map-commutes Data.Fin.suc (tabulate id)) ⟩
  map (flip lookupVec (a ∷V fromList as)) (map Fin.suc (enumerate as))
    ≡⟨ sym (map-∘ (enumerate as)) ⟩
  map (flip lookupVec (a ∷V (fromList as)) ∘ Fin.suc) (enumerate as)
    ≡⟨ refl ⟩
  map (denumerate as) (enumerate as)
    ≡⟨ lemma-map-denumerate-enumerate as ⟩
  as ∎)

theorem-1 : (get : {α : Set} → List α → List α) → {τ : Set} → (eq : EqInst τ) → (s : List τ) → bff get eq s (get s) ≡ just s
theorem-1 get eq s = begin
  bff get eq s (get s)
    ≡⟨ cong (bff get eq s ∘ get) (sym (lemma-map-denumerate-enumerate s)) ⟩
  bff get eq s (get (map (denumerate s) (enumerate s)))
    ≡⟨ cong (bff get eq s) (free-theorem-list-list get (denumerate s) (enumerate s)) ⟩
  bff get eq s (map (denumerate s) (get (enumerate s)))
    ≡⟨ refl ⟩
  fmap (flip map (enumerate s) ∘ flip lookup) (fmap (flip union (fromFunc (denumerate s))) (assoc eq (get (enumerate s)) (map (denumerate s) (get (enumerate s)))))
    ≡⟨ cong (fmap (flip map (enumerate s) ∘ flip lookup) ∘ fmap (flip union (fromFunc (denumerate s)))) (lemma-1 eq (denumerate s) (get (enumerate s))) ⟩
  fmap (flip map (enumerate s) ∘ flip lookup) (fmap (flip union (fromFunc (flip lookupVec (fromList s)))) (just (restrict (denumerate s) (get (enumerate s)))))
    ≡⟨ refl ⟩
  just ((flip map (enumerate s) ∘ flip lookup) (union (restrict (denumerate s) (get (enumerate s))) (fromFunc (denumerate s))))
    ≡⟨ cong just (cong (flip map (enumerate s) ∘ flip lookup) (lemma-union-restrict (denumerate s) (get (enumerate s)))) ⟩
  just ((flip map (enumerate s) ∘ flip lookup) (fromFunc (denumerate s)))
    ≡⟨ refl ⟩
  just (map (flip lookup (fromFunc (denumerate s))) (enumerate s))
    ≡⟨ cong just (map-cong (lookup∘tabulate (denumerate s)) (enumerate s)) ⟩
  just (map (denumerate s) (enumerate s))
    ≡⟨ cong just (lemma-map-denumerate-enumerate s) ⟩
  just s ∎

theorem-2 : (get : {α : Set} → List α → List α) → {τ : Set} → (eq : EqInst τ) → (v s u : List τ) → bff get eq s v ≡ just u → get u ≡ v
theorem-2 get eq v s u p = {!!}
