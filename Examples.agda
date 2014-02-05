module Examples where

open import Data.Nat using (ℕ ; zero ; suc ; _⊓_ ; _∸_)
open import Data.Vec using (Vec ; [] ; _∷_ ; reverse ; _++_)

import GetTypes
import FreeTheorems

open GetTypes.VecVec using (Get)
open FreeTheorems.VecVec using (assume-get)

reverse' : Get
reverse' = assume-get reverse

double' : Get
double' = assume-get f
  where g : ℕ → ℕ
        g zero = zero
        g (suc n) = suc (suc (g n))
        f : {A : Set} {n : ℕ} → Vec A n → Vec A (g n)
        f []      = []
        f (x ∷ v) = x ∷ x ∷ f v

double'' : Get
double'' = assume-get (λ v → v ++ v)

take' : ℕ → Get
take' n = assume-get (f n)
  where f : (n : ℕ) → {A : Set} {m : ℕ} → Vec A m → Vec A (m ⊓ n)
        f n       []       = []
        f zero    (x ∷ xs) = []
        f (suc n) (x ∷ xs) = x ∷ f n xs

drop' : ℕ → Get
drop' n = assume-get (f n)
  where f : (n : ℕ) → {A : Set} {m : ℕ} → Vec A m → Vec A (m ∸ n)
        f zero    xs       = xs
        f (suc n) []       = []
        f (suc n) (x ∷ xs) = f n xs
