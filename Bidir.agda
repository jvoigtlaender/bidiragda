module Bidir where

open import Data.Bool hiding (_≟_)
open import Data.Nat
open import Data.Fin
open import Data.Fin.Props renaming (_≟_ to _≟F_)
open import Data.Maybe
open import Data.List hiding (replicate)
open import Data.Vec hiding (map ; zip ; _>>=_) renaming (lookup to lookupVec)
open import Data.Product hiding (zip ; map)
open import Function
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
_>>=_ = flip (flip maybe′ nothing)

fmap : {A B : Set} → (A → B) → Maybe A → Maybe B
fmap f = maybe′ (λ a → just (f a)) nothing

module FinMap where

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

open FinMap

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

generate : {A : Set} {n : ℕ} → (Fin n → A) → List (Fin n) → FinMapMaybe n A
generate f is = fromAscList (zip is (map f is))

lemma-insert-same : {τ : Set} {n : ℕ} → (m : FinMapMaybe n τ) → (f : Fin n) → (a : τ) → lookupM f m ≡ just a → m ≡ insert f a m
lemma-insert-same []               ()      a p
lemma-insert-same (.(just a) ∷ xs) zero    a refl = refl
lemma-insert-same (x ∷ xs)         (suc i) a p    = cong (_∷_ x) (lemma-insert-same xs i a p)

lemma-lookupM-empty : {A : Set} {n : ℕ} → (i : Fin n) → lookupM {A} i empty ≡ nothing
lemma-lookupM-empty zero    = refl
lemma-lookupM-empty (suc i) = lemma-lookupM-empty i

lemma-from-just : {A : Set} → {x y : A} → _≡_ {_} {Maybe A} (just x) (just y) → x ≡ y
lemma-from-just refl = refl

lemma-lookupM-insert : {A : Set} {n : ℕ} → (i : Fin n) → (a : A) → (m : FinMapMaybe n A) → lookupM i (insert i a m) ≡ just a
lemma-lookupM-insert zero    _ (_ ∷ _)  = refl
lemma-lookupM-insert (suc i) a (_ ∷ xs) = lemma-lookupM-insert i a xs

lemma-lookupM-insert-other : {A : Set} {n : ℕ} → (i j : Fin n) → (a : A) → (m : FinMapMaybe n A) → ¬(i ≡ j) → lookupM i m ≡ lookupM i (insert j a m)
lemma-lookupM-insert-other zero    zero    a m p = contradiction refl p
lemma-lookupM-insert-other zero (suc j) a (x ∷ xs) p = refl
lemma-lookupM-insert-other (suc i) zero a (x ∷ xs) p = refl
lemma-lookupM-insert-other (suc i) (suc j) a (x ∷ xs) p = lemma-lookupM-insert-other i j a xs (contraposition (cong suc) p)

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
lemma-lookupM-generate i f (i' ∷ is) a p with i ≟F i'
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

lemma-checkInsert-generate : {τ : Set} {n : ℕ} → (eq : EqInst τ) → (f : Fin n → τ) → (i : Fin n) → (is : List (Fin n)) → checkInsert eq i (f i) (generate f is) ≡ just (generate f (i ∷ is))
lemma-checkInsert-generate eq f i is with lookupM i (generate f is) | inspect (lookupM i) (generate f is)
lemma-checkInsert-generate eq f i is | nothing | _ = refl
lemma-checkInsert-generate eq f i is | just x | Reveal_is_.[_] prf with lemma-lookupM-generate i f is x prf
lemma-checkInsert-generate eq f i is | just .(f i) | Reveal_is_.[_] prf | refl with eq (f i) (f i)
lemma-checkInsert-generate eq f i is | just .(f i) | Reveal_is_.[_] prf | refl | yes refl = cong just (lemma-insert-same (generate f is) i (f i) prf)
lemma-checkInsert-generate eq f i is | just .(f i) | Reveal_is_.[_] prf | refl | no ¬p = contradiction refl ¬p

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

lemma-2 : {τ : Set} {n : ℕ} → (eq : EqInst τ) → (is : List (Fin n)) → (v : List τ) → (h : FinMapMaybe n τ) → just h ≡ assoc eq is v → map (flip lookup h) is ≡ map just v
lemma-2 eq []       []       h p = refl
lemma-2 eq []       (x ∷ xs) h ()
lemma-2 eq (x ∷ xs) []       h ()
lemma-2 eq (i ∷ is) (x ∷ xs) h p = {!!}

idrange : (n : ℕ) → List (Fin n)
idrange n = toList (tabulate id)

bff : ({A : Set} → List A → List A) → ({B : Set} → EqInst B → List B → List B → Maybe (List B))
bff get eq s v = let s′ = idrange (length s)
                     g  = fromFunc (λ f → lookupVec f (fromList s))
                     h  = assoc eq (get s′) v
                     h′ = fmap (flip union g) h
                 in fmap (flip map s′ ∘ flip lookup) h′

theorem-1 : (get : {α : Set} → List α → List α) → {τ : Set} → (eq : EqInst τ) → (s : List τ) → bff get eq s (get s) ≡ just s
theorem-1 get eq s = {!!}
