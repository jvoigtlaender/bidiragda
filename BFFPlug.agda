open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary using (DecSetoid)

module BFFPlug (A : DecSetoid ℓ₀ ℓ₀) where

open import Data.Nat using (ℕ ; _≟_ ; _+_ ; zero ; suc ; ⌈_/2⌉)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Vec using (Vec)
open import Data.Product using (∃ ; _,_)
open import Relation.Binary using (module DecSetoid)
open import Relation.Binary.PropositionalEquality using (refl ; cong ; subst ; sym ; module ≡-Reasoning) renaming (setoid to PropEq)
open import Relation.Nullary using (yes ; no)
open import Function using (flip ; id ; _∘_)
open import Function.LeftInverse using (_RightInverseOf_)
import Category.Monad
open Category.Monad.RawMonad {ℓ₀} Data.Maybe.monad using (_>>=_)

open import Generic using (sequenceV ; ≡-to-Π)
import BFF
import GetTypes
import Examples

open DecSetoid A using (Carrier)
open GetTypes.PartialVecVec public using (Get)
open BFF.PartialVecBFF A public using (sbff ; bff)

bffsameshape : (G : Get) → {i : Get.|I| G} → Vec Carrier (Get.|gl₁| G i) → Vec Carrier (Get.|gl₂| G i) → Maybe (Vec Carrier (Get.|gl₁| G i))
bffsameshape G {i} = sbff G i

bffplug : (G : Get) → (Get.|I| G → ℕ → Maybe (Get.|I| G)) → {i : Get.|I| G} → {m : ℕ} → Vec Carrier (Get.|gl₁| G i) → Vec Carrier m → Maybe (∃ λ j → Vec (Maybe Carrier) (Get.|gl₁| G j))
bffplug G sput {i} {m} s v with sput i m
...                        | nothing = nothing
...                        | just j with Get.|gl₂| G j ≟ m
...                                 | no gl₂j≢m  = nothing
bffplug G sput {i}     s v | just j | yes refl with bff G j s v
...                                            | nothing = nothing
...                                            | just s′ = just (j , s′)

_SimpleRightInvOf_ : {A B : Set} → (A → B) → (B → A) → Set
f SimpleRightInvOf g = ≡-to-Π f RightInverseOf ≡-to-Π g

bffinv : (G : Get) → (nelteg : ℕ → Get.I G) → nelteg SimpleRightInvOf Get.gl₂ G → {i : Get.|I| G} → {m : ℕ} → Vec Carrier (Get.|gl₁| G i) → Vec Carrier m → Maybe (Vec (Maybe Carrier) (Get.|gl₁| G (nelteg m)))
bffinv G nelteg inv {m = m} s v = bff G (nelteg m) s (subst (Vec Carrier) (sym (inv m)) v)

module InvExamples where
  open Examples using (reverse' ; drop' ; sieve' ; tail' ; take')
  
  reverse-put : {n m : ℕ} → Vec Carrier n → Vec Carrier m → Maybe (Vec Carrier m)
  reverse-put s v = bffinv reverse' id (λ _ → refl) s v >>= sequenceV

  drop-put : (k : ℕ) → {n m : ℕ} → Vec Carrier (k + n) → Vec Carrier m → Maybe (Vec (Maybe Carrier) (k + m))
  drop-put k = bffinv (drop' k) id (λ _ → refl)

  double : ℕ → ℕ
  double zero    = zero
  double (suc n) = suc (suc (double n))

  sieve-inv-len : double SimpleRightInvOf ⌈_/2⌉
  sieve-inv-len zero          = refl
  sieve-inv-len (suc zero)    = refl
  sieve-inv-len (suc (suc x)) = cong (suc ∘ suc) (sieve-inv-len x)

  sieve-put : {n m : ℕ} → Vec Carrier n → Vec Carrier m → Maybe (Vec (Maybe Carrier) (double m))
  sieve-put = bffinv sieve' double sieve-inv-len

  tail-put : {n m : ℕ} → Vec Carrier (suc n) → Vec Carrier m → Maybe (Vec (Maybe Carrier) (suc m))
  tail-put = bffinv tail' id (λ _ → refl)

  take-put : (k : ℕ) → {n : ℕ}  → Vec Carrier (k + n) → Vec Carrier k → Maybe (Vec Carrier (k + n))
  take-put k = bffsameshape (take' k)
