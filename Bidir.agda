module Bidir where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe ; nothing ; just ; maybe′)
open import Data.List using (List ; [] ; _∷_ ; map ; length)
open import Data.List.Properties using (map-cong) renaming (map-compose to map-∘)
open import Data.Vec using (toList ; fromList ; tabulate) renaming (lookup to lookupVec ; _∷_ to _∷V_)
open import Data.Vec.Properties using (tabulate-∘ ; lookup∘tabulate)
open import Data.Empty using (⊥-elim)
open import Function using (id ; _∘_ ; flip)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; Reveal_is_ ; _≗_ ; trans)
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

lemma-just-nothing : {A : Set} → {a : A} → ¬ (_≡_ {_} {Maybe A} (just a) nothing)
lemma-just-nothing ()

lemma-lookupM-assoc : {A : Set} {n : ℕ} → (eq : EqInst A) → (i : Fin n) → (is : List (Fin n)) → (x : A) → (xs : List A) → (h : FinMapMaybe n A) → assoc eq (i ∷ is) (x ∷ xs) ≡ just h → lookupM i h ≡ just x
lemma-lookupM-assoc eq i is x xs h    p with assoc eq is xs
lemma-lookupM-assoc eq i is x xs h    () | nothing
lemma-lookupM-assoc eq i is x xs h    p | just h' = apply-checkInsertProof eq i x h' record
  { same  = λ lookupM≡justx → begin
      lookupM i h
        ≡⟨ cong (lookupM i) (lemma-from-just (trans (sym p) (lemma-checkInsert-same eq i x h' lookupM≡justx))) ⟩
      lookupM i h'
        ≡⟨ lookupM≡justx ⟩
      just x ∎
  ; new   = λ lookupM≡nothing → begin
      lookupM i h
        ≡⟨ cong (lookupM i) (lemma-from-just (trans (sym p) (lemma-checkInsert-new eq i x h' lookupM≡nothing))) ⟩
      lookupM i (insert i x h')
        ≡⟨ lemma-lookupM-insert i x h' ⟩
      just x ∎
  ; wrong = λ x' x≢x' lookupM≡justx' → ⊥-elim (lemma-just-nothing (trans (sym p) (lemma-checkInsert-wrong eq i x h' x' x≢x' lookupM≡justx')))
  }

lemma-2 : {τ : Set} {n : ℕ} → (eq : EqInst τ) → (is : List (Fin n)) → (v : List τ) → (h : FinMapMaybe n τ) → assoc eq is v ≡ just h → map (flip lookupM h) is ≡ map just v
lemma-2 eq []       []       h p = refl
lemma-2 eq []       (x ∷ xs) h ()
lemma-2 eq (x ∷ xs) []       h ()
lemma-2 eq (i ∷ is) (x ∷ xs) h p with assoc eq is xs | inspect (assoc eq is) xs
lemma-2 eq (i ∷ is) (x ∷ xs) h () | nothing | _
lemma-2 eq (i ∷ is) (x ∷ xs) h p | just h' | Reveal_is_.[_] ir = begin
  map (flip lookupM h) (i ∷ is)
    ≡⟨ refl ⟩
  lookupM i h ∷ map (flip lookupM h) is
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
