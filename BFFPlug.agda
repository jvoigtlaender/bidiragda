open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary using (DecSetoid)

module BFFPlug (A : DecSetoid ℓ₀ ℓ₀) where

open import Data.Nat using (ℕ ; _≟_ ; _+_ ; _∸_ ; zero ; suc ; ⌈_/2⌉)
open import Data.Nat.Properties using (m+n∸n≡m)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Vec using (Vec)
open import Data.Product using (∃ ; _,_)
open import Relation.Binary using (module DecSetoid)
open import Relation.Binary.PropositionalEquality using (refl ; cong ; subst ; sym ; module ≡-Reasoning) renaming (setoid to PropEq)
open import Relation.Nullary using (yes ; no)
open import Function using (flip ; id ; _∘_)
open import Function.Equality using (_⟶_)
open import Function.LeftInverse using (_RightInverseOf_)

import BFF
import GetTypes
import Examples

open DecSetoid A using (Carrier)
open GetTypes.VecVec public using (Get)
open BFF.VecBFF A public

bffsameshape : (G : Get) → {n : ℕ} → Vec Carrier n → Vec Carrier (Get.getlen G n) → Maybe (Vec Carrier n)
bffsameshape G {n} = bff G n

bffplug : (G : Get) → (ℕ → ℕ → Maybe ℕ) → {n m : ℕ} → Vec Carrier n → Vec Carrier m → Maybe (∃ λ l → Vec Carrier l)
bffplug G sput {n} {m} s v with sput n m
...                        | nothing = nothing
...                        | just l with Get.getlen G l ≟ m
...                                 | no getlenl≢m  = nothing
bffplug G sput {n}     s v | just l | yes refl with bff G l s v
...                                            | nothing = nothing
...                                            | just s′ = just (l , s′)

as-Π : {A B : Set} → (f : A → B) → PropEq A ⟶ PropEq B
as-Π f = record { _⟨$⟩_ = f; cong = cong f }

_SimpleRightInvOf_ : (ℕ → ℕ) → (ℕ → ℕ) → Set
f SimpleRightInvOf g = as-Π f RightInverseOf as-Π g

bffinv : (G : Get) → (nelteg : ℕ → ℕ) → nelteg SimpleRightInvOf Get.getlen G → {n m : ℕ} → Vec Carrier n → Vec Carrier m → Maybe (Vec Carrier (nelteg m))
bffinv G nelteg inv {n} {m} s v = bff G (nelteg m) s (subst (Vec Carrier) (sym (inv m)) v)

module InvExamples where
  open Examples using (reverse' ; drop' ; sieve')
  
  reverse-put : {n m : ℕ} → Vec Carrier n → Vec Carrier m → Maybe (Vec Carrier m)
  reverse-put = bffinv reverse' id (λ _ → refl)

  drop-put : (k : ℕ) → {n m : ℕ} → Vec Carrier n → Vec Carrier m → Maybe (Vec Carrier (m + k))
  drop-put k = bffinv (drop' k) (flip _+_ k) (flip m+n∸n≡m k)

  double : ℕ → ℕ
  double zero    = zero
  double (suc n) = suc (suc (double n))

  sieve-inv-len : double SimpleRightInvOf ⌈_/2⌉
  sieve-inv-len zero          = refl
  sieve-inv-len (suc zero)    = refl
  sieve-inv-len (suc (suc x)) = cong (suc ∘ suc) (sieve-inv-len x)

  sieve-put : {n m : ℕ} → Vec Carrier n → Vec Carrier m → Maybe (Vec Carrier (double m))
  sieve-put = bffinv sieve' double sieve-inv-len
