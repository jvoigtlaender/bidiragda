open import Relation.Binary.Core using (Decidable ; _≡_)

module Precond (Carrier : Set) (deq : Decidable {A = Carrier} _≡_) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; toList)
import Data.List.Any
open Data.List.Any.Membership-≡ using (_∉_)
open import Data.Maybe using (just)
open import Data.Product using (∃ ; _,_)
open import Function using (flip ; _∘_)
open import Relation.Binary.PropositionalEquality using (refl ; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

open import FinMap using (FinMap ; FinMapMaybe ; union ; fromFunc ; empty ; insert)
import CheckInsert
open CheckInsert Carrier deq using (checkInsert ; lemma-checkInsert-new)
open import BFF using (fmap ; _>>=_)
import Bidir
open Bidir Carrier deq using (lemma-∉-lookupM-assoc)

open BFF.VecBFF Carrier deq using (get-type ; assoc ; enumerate ; denumerate ; bff)

assoc-enough : {getlen : ℕ → ℕ} (get : get-type getlen) → {m : ℕ} → (s : Vec Carrier m) → (v : Vec Carrier (getlen m)) → ∃ (λ h → assoc (get (enumerate s)) v ≡ just h) → ∃ λ u → bff get s v ≡ just u
assoc-enough get s v (h , p) = u , cong (fmap (flip map s′ ∘ flip lookup) ∘ (fmap (flip union g))) p
    where s′ = enumerate s
          g  = fromFunc (denumerate s)
          u  = map (flip lookup (union h g)) s′

data All-different {A : Set} : {n : ℕ} → Vec A n → Set where
  different-[] : All-different []
  different-∷  : {n : ℕ} {x : A} {xs : Vec A n} → x ∉ toList xs → All-different xs → All-different (x ∷ xs)

different-assoc : {m n : ℕ} → (u : Vec (Fin n) m) → (v : Vec Carrier m) → All-different u → ∃ λ h → assoc u v ≡ just h
different-assoc []       []       p = empty , refl
different-assoc (u ∷ us) (v ∷ vs) (different-∷ u∉us diff-us) with different-assoc us vs diff-us
different-assoc (u ∷ us) (v ∷ vs) (different-∷ u∉us diff-us) | h , p' = insert u v h , (begin
  assoc (u ∷ us) (v ∷ vs)
    ≡⟨ refl ⟩
  assoc us vs >>= checkInsert u v
    ≡⟨ cong (flip _>>=_ (checkInsert u v)) p' ⟩
  checkInsert u v h
    ≡⟨ lemma-checkInsert-new u v h (lemma-∉-lookupM-assoc u us vs h p' u∉us) ⟩
  just (insert u v h) ∎)
