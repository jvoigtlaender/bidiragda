module Examples where

open import Data.Nat using (ℕ ; zero ; suc ; _⊓_ ; _∸_ ; ⌈_/2⌉)
open import Data.Vec using (Vec ; [] ; _∷_ ; reverse ; _++_)
open import Function using (id)
open import Function.Injection using () renaming (id to id↪)

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

take' : ℕ → Get
take' n = assume-get id↪ (≡-to-Π _) (f n)
  where f : (n : ℕ) → {A : Set} {m : ℕ} → Vec A m → Vec A (m ⊓ n)
        f n       []       = []
        f zero    (x ∷ xs) = []
        f (suc n) (x ∷ xs) = x ∷ f n xs

drop' : ℕ → Get
drop' n = assume-get id↪ (≡-to-Π _) (f n)
  where f : (n : ℕ) → {A : Set} {m : ℕ} → Vec A m → Vec A (m ∸ n)
        f zero    xs       = xs
        f (suc n) []       = []
        f (suc n) (x ∷ xs) = f n xs

sieve' : Get
sieve' = assume-get id↪ (≡-to-Π _) f
  where f : {A : Set} {n : ℕ} → Vec A n → Vec A ⌈ n /2⌉
        f []           = []
        f (x ∷ [])     = x ∷ []
        f (x ∷ _ ∷ xs) = x ∷ f xs
