module Generic where

import Category.Functor
import Category.Monad
open import Data.List using (List ; length ; replicate) renaming ([] to []L ; _∷_ to _∷L_)
open import Data.Maybe using (Maybe ; just ; nothing) renaming (setoid to MaybeEq)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using (Vec ; toList ; fromList ; map) renaming ([] to []V ; _∷_ to _∷V_)
open import Data.Vec.Equality using () renaming (module Equality to VecEq)
open import Function using (_∘_)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary using (Setoid ; module Setoid)
open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Binary.Indexed using (_at_) renaming (Setoid to ISetoid)
open import Relation.Binary.PropositionalEquality using (_≗_ ; cong ; subst ; trans) renaming (setoid to PropEq)

open Category.Functor.RawFunctor {Level.zero} Data.Maybe.functor using (_<$>_)
open Category.Monad.RawMonad {Level.zero} Data.Maybe.monad using (_>>=_)

∷-injective : {A : Set} {n : ℕ} {x y : A} {xs ys : Vec A n} →
              (x ∷V xs) ≡ (y ∷V ys) → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

just-injective : {A : Set} → {x y : A} → Maybe.just x ≡ Maybe.just y → x ≡ y
just-injective refl = refl

length-replicate : {A : Set} {a : A} → (n : ℕ) → length (replicate n a) ≡ n
length-replicate zero       = refl
length-replicate (suc n) = cong suc (length-replicate n)

map-just-injective : {A : Set} {n : ℕ} {xs ys : Vec A n} →
                     map Maybe.just xs ≡ map Maybe.just ys → xs ≡ ys
map-just-injective {xs = []V}      {ys = []V}       p  = refl
map-just-injective {xs = x ∷V xs′} {ys = y ∷V ys′}  p with ∷-injective p
map-just-injective {xs = x ∷V xs′} {ys = .x ∷V ys′} p | refl , p′ = cong (_∷V_ x) (map-just-injective p′)

mapMV : {A B : Set} {n : ℕ} → (A → Maybe B) → Vec A n → Maybe (Vec B n)
mapMV f []V = just []V
mapMV f (x ∷V xs) = (f x) >>= (λ y → (_∷V_ y) <$> (mapMV f xs))

mapMV-cong : {A B : Set} {f g : A → Maybe B} → f ≗ g → {n : ℕ} → mapMV {n = n} f ≗ mapMV g
mapMV-cong f≗g []V = refl
mapMV-cong {f = f} {g = g} f≗g (x ∷V xs) with f x | g x | f≗g x
mapMV-cong f≗g (x ∷V xs) | just y | .(just y) | refl = cong (_<$>_ (_∷V_ y)) (mapMV-cong f≗g xs)
mapMV-cong f≗g (x ∷V xs) | nothing | .nothing | refl = refl

mapMV-purity : {A B : Set} {n : ℕ} → (f : A → B) → (v : Vec A n) → mapMV (just ∘ f) v ≡ just (map f v)
mapMV-purity f []V = refl
mapMV-purity f (x ∷V xs) rewrite mapMV-purity f xs = refl

maybeEq-from-≡ : {A : Set} {a b : Maybe A} → Setoid._≈_ (PropEq (Maybe A)) a b → Setoid._≈_ (MaybeEq (PropEq A)) a b
maybeEq-from-≡ {a = just x}  {b = .(just x)} refl = just refl
maybeEq-from-≡ {a = nothing} {b = .nothing}  refl = nothing

maybeEq-to-≡ : {A : Set} {a b : Maybe A} → Setoid._≈_ (MaybeEq (PropEq A)) a b → Setoid._≈_ (PropEq (Maybe A)) a b
maybeEq-to-≡ (just refl) = refl
maybeEq-to-≡ nothing     = refl

subst-cong : {A : Set} → (T : A → Set) → {g : A → A} → {a b : A} → (f : {c : A} → T c → T (g c)) → (p : a ≡ b) →
             f ∘ subst T p ≗ subst T (cong g p) ∘ f
subst-cong T f refl _ = refl

subst-fromList : {A : Set} {x y : List A} → (p : y ≡ x) →
                 subst (Vec A) (cong length p) (fromList y) ≡ fromList x
subst-fromList refl = refl

subst-subst : {A : Set} (T : A → Set) {a b c : A} → (p : a ≡ b) → (p′ : b ≡ c) → (x : T a) →
              subst T p′ (subst T p x) ≡ subst T (trans p p′) x
subst-subst T refl p′ x = refl

toList-fromList : {A : Set} → (l : List A) → toList (fromList l) ≡ l
toList-fromList []L       = refl
toList-fromList (x ∷L xs) = cong (_∷L_ x) (toList-fromList xs)

toList-subst : {A : Set} → {n m : ℕ} (v : Vec A n) → (p : n ≡ m) →
               toList (subst (Vec A) p v) ≡ toList v
toList-subst v refl = refl

vecIsISetoid : Setoid ℓ₀ ℓ₀ → ISetoid ℕ ℓ₀ ℓ₀
vecIsISetoid S = record
  { Carrier = Vec (Setoid.Carrier S)
  ; _≈_ = λ x → S VecEq.≈ x
  ; isEquivalence = record
    { refl = VecEq.refl S _
    ; sym = VecEq.sym S
    ; trans = VecEq.trans S }
  }


vecIsSetoid : Setoid ℓ₀ ℓ₀ → ℕ → Setoid ℓ₀ ℓ₀
vecIsSetoid S n = (vecIsISetoid S) at n