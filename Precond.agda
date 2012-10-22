open import Relation.Binary.Core using (Decidable ; _≡_)

module Precond (Carrier : Set) (deq : Decidable {A = Carrier} _≡_) where

open import Data.Nat using (ℕ) renaming (zero to nzero ; suc to nsuc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; toList)
open import Data.List.Any using (here ; there)
open Data.List.Any.Membership-≡ using (_∉_)
open import Data.Maybe using (just)
open import Data.Product using (∃ ; _,_)
open import Function using (flip ; _∘_)
open import Relation.Binary.Core using (_≢_)
open import Relation.Binary.PropositionalEquality using (refl ; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

open import FinMap using (FinMap ; FinMapMaybe ; union ; fromFunc ; empty ; insert)
open import CheckInsert using (EqInst ; checkInsert ; lemma-checkInsert-new)
open import BFF using (fmap ; _>>=_)
import Bidir
open Bidir Carrier deq using (lemma-∉-lookupM-assoc)

open BFF.VecBFF Carrier deq using (get-type ; assoc ; enumerate ; denumerate ; bff)

assoc-enough : {getlen : ℕ → ℕ} (get : get-type getlen) → {m : ℕ} → (s : Vec Carrier m) → (v : Vec Carrier (getlen m)) → (h : FinMapMaybe m Carrier) → assoc (get (enumerate s)) v ≡ just h → ∃ λ u → bff get s v ≡ just u
assoc-enough get {m} s v h p = map (flip lookup (union h g)) s′ , (begin
  bff get s v
    ≡⟨ refl ⟩
  fmap (flip map s′ ∘ flip lookup) (fmap (flip union g) (assoc (get s′) v))
    ≡⟨ cong (fmap (flip map s′ ∘ flip lookup)) (cong (fmap (flip union g)) p) ⟩
  fmap (flip map s′ ∘ flip lookup) (fmap (flip union g) (just h))
    ≡⟨ refl ⟩
  just (map (flip lookup (union h g)) s′) ∎)
    where s′ : Vec (Fin m) m
          s′ = enumerate s
          g : FinMap m Carrier
          g = fromFunc (denumerate s)

all-different : {A : Set} {n : ℕ} → Vec A n → Set
all-different {_} {n} v = (i : Fin n) → (j : Fin n) → i ≢ j → lookup i v ≢ lookup j v

suc-injective : {n : ℕ} {i j : Fin n} → (suc i ≡ suc j) → i ≡ j
suc-injective refl = refl

different-swap : {A : Set} {n : ℕ} → (a b : A) → (v : Vec A n) → all-different (a ∷ b ∷ v) → all-different (b ∷ a ∷ v)
different-swap a b v p zero          zero          i≢j li≡lj = i≢j refl
different-swap a b v p zero          (suc zero)    i≢j li≡lj = p (suc zero) zero (λ ()) li≡lj
different-swap a b v p zero          (suc (suc j)) i≢j li≡lj = p (suc zero) (suc (suc j)) (λ ()) li≡lj
different-swap a b v p (suc zero)    zero          i≢j li≡lj = p zero (suc zero) (λ ()) li≡lj
different-swap a b v p (suc zero)    (suc zero)    i≢j li≡lj = i≢j refl
different-swap a b v p (suc zero)    (suc (suc j)) i≢j li≡lj = p zero (suc (suc j)) (λ ()) li≡lj
different-swap a b v p (suc (suc i)) zero          i≢j li≡lj = p (suc (suc i)) (suc zero) (λ ()) li≡lj
different-swap a b v p (suc (suc i)) (suc zero)    i≢j li≡lj = p (suc (suc i)) zero (λ ()) li≡lj
different-swap a b v p (suc (suc i)) (suc (suc j)) i≢j li≡lj = p (suc (suc i)) (suc (suc j)) i≢j li≡lj

different-drop : {A : Set} {n : ℕ} → (a : A) → (v : Vec A n) → all-different (a ∷ v) → all-different v
different-drop a v p i j i≢j = p (suc i) (suc j) (i≢j ∘ suc-injective)

different-∉ : {A : Set} {n : ℕ} → (x : A) (xs : Vec A n) → all-different (x ∷ xs) → x ∉ (toList xs)
different-∉ x [] p ()
different-∉ x (y ∷ ys) p (here px) = p zero (suc zero) (λ ()) px
different-∉ x (y ∷ ys) p (there pxs) = different-∉ x ys (different-drop y (x ∷ ys) (different-swap x y ys p)) pxs

different-assoc : {m n : ℕ} → (u : Vec (Fin n) m) → (v : Vec Carrier m) → all-different u → ∃ λ h → assoc u v ≡ just h
different-assoc []       []       p = empty , refl
different-assoc (u ∷ us) (v ∷ vs) p with different-assoc us vs (λ i j i≢j → p (suc i) (suc j) (i≢j ∘ suc-injective))
different-assoc (u ∷ us) (v ∷ vs) p | h , p' = insert u v h , (begin
  assoc (u ∷ us) (v ∷ vs)
    ≡⟨ refl ⟩
  assoc us vs >>= checkInsert deq u v
    ≡⟨ cong (flip _>>=_ (checkInsert deq u v)) p' ⟩
  checkInsert deq u v h
    ≡⟨ lemma-checkInsert-new deq u v h (lemma-∉-lookupM-assoc u us vs h p' (different-∉ u us p)) ⟩
  just (insert u v h) ∎)
