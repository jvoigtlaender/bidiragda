module FinMap where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Maybe using (Maybe ; just ; nothing ; maybe′)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Props using (_≟_)
open import Data.Vec using (Vec ; [] ; _∷_ ; _[_]≔_ ; replicate ; tabulate) renaming (lookup to lookupVec)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Data.List using (List ; [] ; _∷_ ; map ; zip)
open import Data.Product using (_×_ ; _,_)
open import Function using (id ; _∘_ ; flip)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Core using (_≡_ ; refl ; _≢_)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; _≗_ ; trans)
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
union m1 m2 = fromFunc (λ f → maybe′ id (lookup f m2) (lookupM f m1))

restrict : {A : Set} {n : ℕ} → (Fin n → A) → List (Fin n) → FinMapMaybe n A
restrict f is = fromAscList (zip is (map f is))

lemma-just≢nothing : {A Whatever : Set} {a : A} → _≡_ {_} {Maybe A} (just a) nothing → Whatever
lemma-just≢nothing ()

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

lemma-lookupM-insert-other : {A : Set} {n : ℕ} → (i j : Fin n) → (a : A) → (m : FinMapMaybe n A) → i ≢ j → lookupM i m ≡ lookupM i (insert j a m)
lemma-lookupM-insert-other zero    zero    a m        p = contradiction refl p
lemma-lookupM-insert-other zero    (suc j) a (x ∷ xs) p = refl
lemma-lookupM-insert-other (suc i) zero    a (x ∷ xs) p = refl
lemma-lookupM-insert-other (suc i) (suc j) a (x ∷ xs) p = lemma-lookupM-insert-other i j a xs (p ∘ cong suc)

just-injective : {A : Set} → {x y : A} → _≡_ {_} {Maybe A} (just x) (just y) → x ≡ y
just-injective refl = refl

lemma-lookupM-restrict : {A : Set} {n : ℕ} → (i : Fin n) → (f : Fin n → A) → (is : List (Fin n)) → (a : A) → lookupM i (restrict f is) ≡ just a → f i ≡ a
lemma-lookupM-restrict i f [] a p = lemma-just≢nothing (trans (sym p) (lemma-lookupM-empty i))
lemma-lookupM-restrict i f (i' ∷ is) a p with i ≟ i'
lemma-lookupM-restrict i f (.i ∷ is) a p | yes refl = just-injective (begin
   just (f i)
     ≡⟨ sym (lemma-lookupM-insert i (f i) (restrict f is)) ⟩
   lookupM i (insert i (f i) (restrict f is))
     ≡⟨ refl ⟩
   lookupM i (restrict f (i ∷ is))
     ≡⟨ p ⟩
   just a ∎)
lemma-lookupM-restrict i f (i' ∷ is) a p | no ¬p2 = lemma-lookupM-restrict i f is a (begin
  lookupM i (restrict f is)
    ≡⟨ lemma-lookupM-insert-other i i' (f i') (restrict f is) ¬p2 ⟩
  lookupM i (insert i' (f i') (restrict f is))
    ≡⟨ refl ⟩
  lookupM i (restrict f (i' ∷ is))
    ≡⟨ p ⟩
  just a ∎)

lemma-tabulate-∘ : {n : ℕ} {A : Set} → {f g : Fin n → A} → f ≗ g → tabulate f ≡ tabulate g
lemma-tabulate-∘ {zero}  {_} {f} {g} f≗g = refl
lemma-tabulate-∘ {suc n} {_} {f} {g} f≗g = begin
  f zero ∷ tabulate (f ∘ suc)
    ≡⟨ cong (flip Vec._∷_ (tabulate (f ∘ suc))) (f≗g zero) ⟩
  g zero ∷ tabulate (f ∘ suc)
    ≡⟨ cong (Vec._∷_ (g zero)) (lemma-tabulate-∘ (f≗g ∘ suc)) ⟩
  g zero ∷ tabulate (g ∘ suc) ∎

lemma-union-restrict : {n : ℕ} {A : Set} → (f : Fin n → A) → (is : List (Fin n)) → union (restrict f is) (fromFunc f) ≡ fromFunc f
lemma-union-restrict {n} f is = begin
  union (restrict f is) (fromFunc f)
    ≡⟨ refl ⟩
  tabulate (λ j → maybe′ id (lookup j (fromFunc f)) (lookupM j (restrict f is)))
    ≡⟨ lemma-tabulate-∘ (lemma-inner is) ⟩
  tabulate f ∎
    where lemma-inner : (is : List (Fin n)) → (j : Fin n) → maybe′ id (lookup j (fromFunc f)) (lookupM j (restrict f is)) ≡ f j
          lemma-inner []       j = begin
            maybe′ id (lookup j (fromFunc f)) (lookupM j empty)
              ≡⟨ cong (maybe′ id (lookup j (fromFunc f))) (lemma-lookupM-empty j) ⟩
            maybe′ id (lookup j (fromFunc f)) nothing
              ≡⟨ refl ⟩
            lookup j (fromFunc f)
              ≡⟨ lookup∘tabulate f j ⟩
            f j ∎
          lemma-inner (i ∷ is)  j with j ≟ i
          lemma-inner (.j ∷ is) j | yes refl = cong (maybe′ id (lookup j (fromFunc f))) (lemma-lookupM-insert j (f j) (restrict f is))
          lemma-inner (i ∷ is)  j | no j≢i = begin
            maybe′ id (lookup j (fromFunc f)) (lookupM j (insert i (f i) (restrict f is)))
              ≡⟨ cong (maybe′ id (lookup j (fromFunc f))) (sym (lemma-lookupM-insert-other j i (f i) (restrict f is) j≢i)) ⟩
            maybe′ id (lookup j (fromFunc f)) (lookupM j (restrict f is))
              ≡⟨ lemma-inner is j ⟩
            f j ∎
