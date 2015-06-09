module Examples where

open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; ⌈_/2⌉)
open import Data.Nat.Properties using (cancel-+-left)
import Algebra.Structures
open import Data.List using (List ; length) renaming ([] to []L ; _∷_ to _∷L_)
open import Data.Vec using (Vec ; [] ; _∷_ ; reverse ; _++_ ; tail ; take ; drop)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import Structures using (Shaped)
import GetTypes
import FreeTheorems

open GetTypes.PartialVecVec using (Get)
open FreeTheorems.PartialVecVec using (assume-get)

reverse' : Get
reverse' = assume-get id id reverse

double' : Get
double' = assume-get id g f
  where g : ℕ → ℕ
        g zero = zero
        g (suc n) = suc (suc (g n))
        f : {A : Set} {n : ℕ} → Vec A n → Vec A (g n)
        f []      = []
        f (x ∷ v) = x ∷ x ∷ f v

double'' : Get
double'' = assume-get id _ (λ v → v ++ v)

tail' : Get
tail' = assume-get suc id tail

take' : ℕ → Get
take' n = assume-get (_+_ n) _ (take n)

drop' : ℕ → Get
drop' n = assume-get (_+_ n) _ (drop n)

sieve' : Get
sieve' = assume-get id _ f
  where f : {A : Set} {n : ℕ} → Vec A n → Vec A ⌈ n /2⌉
        f []           = []
        f (x ∷ [])     = x ∷ []
        f (x ∷ _ ∷ xs) = x ∷ f xs

intersperse-len : ℕ → ℕ
intersperse-len zero          = zero
intersperse-len (suc zero)    = suc zero
intersperse-len (suc (suc n)) = suc (suc (intersperse-len (suc n)))

intersperse : {A : Set} {n : ℕ} → A → Vec A n → Vec A (intersperse-len n)
intersperse s []          = []
intersperse s (x ∷ [])    = x ∷ []
intersperse s (x ∷ y ∷ v) = x ∷ s ∷ intersperse s (y ∷ v)

intersperse' : Get
intersperse' = assume-get suc intersperse-len f
  where f : {A : Set} {n : ℕ} → Vec A (suc n) → Vec A (intersperse-len n)
        f (s ∷ v)        = intersperse s v

data PairVec (α : Set) (β : Set) : List α → Set where
  []P : PairVec α β []L
  _,_∷P_ : (x : α) → β → {l : List α} → PairVec α β l → PairVec α β (x ∷L l)

PairVecFirstShaped : (α : Set) → Shaped (List α) (PairVec α)
PairVecFirstShaped α = record
  { arity = length
  ; content = content
  ; fill = fill
  ; isShaped = record
    { content-fill = content-fill
    ; fill-content = fill-content
    } }
  where content : {β : Set} {s : List α} → PairVec α β s → Vec β (length s)
        content []P          = []
        content (a , b ∷P p) = b ∷ content p

        fill : {β : Set} → (s : List α) → Vec β (length s) → PairVec α β s
        fill []L      v       = []P
        fill (a ∷L s) (b ∷ v) = a , b ∷P fill s v

        content-fill : {β : Set} {s : List α} → (p : PairVec α β s) → fill s (content p) ≡ p
        content-fill []P          = refl
        content-fill (a , b ∷P p) = cong (_,_∷P_ a b) (content-fill p)

        fill-content : {β : Set} → (s : List α) → (v : Vec β (length s)) → content (fill s v) ≡ v
        fill-content []L      []      = refl
        fill-content (a ∷L s) (b ∷ v) = cong (_∷_ b) (fill-content s v)
