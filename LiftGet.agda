module LiftGet where

open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; suc)
open import Data.Vec using (Vec ; toList ; fromList) renaming ([] to []V ; _∷_ to _∷V_)
open import Data.List using (List ; [] ; _∷_ ; length ; replicate ; map)
open import Data.List.Properties using (length-map)
open import Data.Product using (∃ ; _,_ ; proj₂)
open import Function using (_∘_ ; flip ; const)
open import Relation.Binary.Core using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≗_ ; sym ; cong ; refl)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

get-type : Set₁
get-type = {A : Set} → List A → List A

getV-type : (ℕ → ℕ) → Set₁
getV-type getlen = {A : Set} {n : ℕ} → Vec A n → Vec A (getlen n)

getVec-to-getList : {getlen : ℕ → ℕ} → (getV-type getlen) → get-type
getVec-to-getList get = toList ∘ get ∘ fromList

getList-to-getlen : get-type → ℕ → ℕ
getList-to-getlen get = length ∘ get ∘ flip replicate tt

postulate
  free-theorem-list-list : {β γ : Set} → (get : get-type) → (f : β → γ) → get ∘ map f ≗ map f ∘ get

replicate-length : {A : Set} → (l : List A) → map (const tt) l ≡ replicate (length l) tt
replicate-length [] = refl
replicate-length (_ ∷ l) = cong (_∷_ tt) (replicate-length l)

getList-length : (get : get-type) → {B : Set} → (l : List B) → length (get l) ≡ getList-to-getlen get (length l)
getList-length get l = begin
  length (get l)
    ≡⟨ sym (length-map (const tt) (get l)) ⟩
  length (map (const tt) (get l))
    ≡⟨ cong length (sym (free-theorem-list-list get (const tt) l)) ⟩
  length (get (map (const tt) l))
    ≡⟨ cong (length ∘ get) (replicate-length l) ⟩
  length (get (replicate (length l) tt)) ∎

length-toList : {A : Set} {n : ℕ} → (v : Vec A n) → length (toList v) ≡ n
length-toList []V = refl
length-toList (x ∷V xs) = cong suc (length-toList xs) 

vec-length : {A : Set} {n m : ℕ} → n ≡ m → Vec A n → Vec A m
vec-length refl v = v

getList-to-getVec : get-type → ∃ λ (getlen : ℕ → ℕ) → (getV-type getlen)
getList-to-getVec get = getlen , get'
  where getlen : ℕ → ℕ
        getlen = getList-to-getlen get
        length-prop : {C : Set} → (m : ℕ) → (v : Vec C m) → length (get (toList v)) ≡ length (get (replicate m tt))
        length-prop m v = begin
            length (get (toList v))
              ≡⟨ getList-length get (toList v) ⟩
            length (get (replicate (length (toList v)) tt))
              ≡⟨ cong (length ∘ get ∘ flip replicate tt) (length-toList v) ⟩
            length (get (replicate m tt)) ∎
        get' : {C : Set} {m : ℕ} → Vec C m → Vec C (getlen m)
        get' {_} {m} v = vec-length (length-prop m v) (fromList (get (toList v)))

get-trafo-1 : (get : get-type) → {B : Set} → getVec-to-getList (proj₂ (getList-to-getVec get)) {B} ≗ get {B}
get-trafo-1 get l = begin
  getVec-to-getList (proj₂ (getList-to-getVec get)) l
    ≡⟨ {!!} ⟩
  get l ∎