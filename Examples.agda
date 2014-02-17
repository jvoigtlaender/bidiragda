module Examples where

open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; ⌈_/2⌉)
open import Data.Nat.Properties using (cancel-+-left)
import Algebra.Structures
open Algebra.Structures.IsCommutativeSemiring Data.Nat.Properties.isCommutativeSemiring using (+-isCommutativeMonoid)
open Algebra.Structures.IsCommutativeMonoid +-isCommutativeMonoid using () renaming (comm to +-comm)
open import Data.Vec using (Vec ; [] ; _∷_ ; reverse ; _++_ ; tail ; take ; drop)
open import Function using (id)
open import Function.Injection using () renaming (Injection to _↪_ ; id to id↪)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl) renaming (setoid to EqSetoid)

open import Generic using (≡-to-Π)
import GetTypes
import FreeTheorems

open GetTypes.PartialVecVec using (Get)
open FreeTheorems.PartialVecVec using (assume-get)

reverse' : Get
reverse' = assume-get id↪ (≡-to-Π id) reverse

double' : Get
double' = assume-get id↪ (≡-to-Π g) f
  where g : ℕ → ℕ
        g zero = zero
        g (suc n) = suc (suc (g n))
        f : {A : Set} {n : ℕ} → Vec A n → Vec A (g n)
        f []      = []
        f (x ∷ v) = x ∷ x ∷ f v

double'' : Get
double'' = assume-get id↪ (≡-to-Π _) (λ v → v ++ v)

drop-suc : {n m : ℕ} → suc n ≡ suc m → n ≡ m
drop-suc refl = refl

suc-injection : EqSetoid ℕ ↪ EqSetoid ℕ
suc-injection = record { to = ≡-to-Π suc; injective = drop-suc }

tail' : Get
tail' = assume-get suc-injection (≡-to-Π id) tail

n+-injection : ℕ → EqSetoid ℕ ↪ EqSetoid ℕ
n+-injection n = record { to = ≡-to-Π (_+_ n); injective = cancel-+-left n }

take' : ℕ → Get
take' n = assume-get (n+-injection n) (≡-to-Π _) (take n)

drop' : ℕ → Get
drop' n = assume-get (n+-injection n) (≡-to-Π _) (drop n)

sieve' : Get
sieve' = assume-get id↪ (≡-to-Π _) f
  where f : {A : Set} {n : ℕ} → Vec A n → Vec A ⌈ n /2⌉
        f []           = []
        f (x ∷ [])     = x ∷ []
        f (x ∷ _ ∷ xs) = x ∷ f xs
