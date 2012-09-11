module LiftGet where

open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; suc)
open import Data.Vec using (Vec ; toList ; fromList) renaming ([] to []V ; _∷_ to _∷V_)
open import Data.List using (List ; [] ; _∷_ ; length ; replicate ; map)
open import Data.List.Properties using (length-map)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Function using (_∘_ ; flip ; const)
open import Relation.Binary.Core using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≗_ ; sym ; cong ; refl ; subst ; proof-irrelevance)
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

toList-fromList : {A : Set} → (l : List A) → toList (fromList l) ≡ l
toList-fromList []       = refl
toList-fromList (x ∷ xs) = cong (_∷_ x) (toList-fromList xs)

toList-subst : {A : Set} → {n m : ℕ} (v : Vec A n) → (p : n ≡ m) → toList (subst (Vec A) p v) ≡ toList v
toList-subst v refl = refl

getList-to-getVec-length-property : (get : get-type) → {C : Set} → {m : ℕ} → (v : Vec C m) → length (get (toList v)) ≡ length (get (replicate m tt))
getList-to-getVec-length-property get {_} {m} v = begin
    length (get (toList v))
      ≡⟨ getList-length get (toList v) ⟩
    length (get (replicate (length (toList v)) tt))
      ≡⟨ cong (length ∘ get ∘ flip replicate tt) (length-toList v) ⟩
    length (get (replicate m tt)) ∎

getList-to-getVec : get-type → ∃ λ (getlen : ℕ → ℕ) → (getV-type getlen)
getList-to-getVec get = getlen , get'
  where getlen : ℕ → ℕ
        getlen = getList-to-getlen get
        get' : {C : Set} {m : ℕ} → Vec C m → Vec C (getlen m)
        get' {C} v = subst (Vec C) (getList-to-getVec-length-property get v) (fromList (get (toList v)))

{-
-- We cannot formulate the first commutation property, because the type of
-- fromList (get l) depends on the concrete l, more specifically its length.
get-commut-1 : (get : get-type) → (fromList ∘ get) ≗ (proj₂ (getList-to-getVec get)) ∘ fromList
get-commut-1 get l = ?
-}

get-trafo-1 : (get : get-type) → {B : Set} → getVec-to-getList (proj₂ (getList-to-getVec get)) {B} ≗ get {B}
get-trafo-1 get {B} l = begin
  getVec-to-getList (proj₂ (getList-to-getVec get)) l
    ≡⟨ refl ⟩
  toList (proj₂ (getList-to-getVec get) (fromList l))
    ≡⟨ refl ⟩
  toList (subst (Vec B) (getList-to-getVec-length-property get (fromList l)) (fromList (get (toList (fromList l)))))
    ≡⟨ toList-subst (fromList (get (toList (fromList l)))) (getList-to-getVec-length-property get (fromList l)) ⟩
  toList (fromList (get (toList (fromList l))))
    ≡⟨ toList-fromList (get (toList (fromList l))) ⟩
  get (toList (fromList l))
    ≡⟨ cong get (toList-fromList l) ⟩
  get l ∎

vec-len : {A : Set} {n : ℕ} → Vec A n → ℕ
vec-len {_} {n} _ = n

vec-len-via-list : {A : Set} {n : ℕ} → (v : Vec A n) → length (toList v) ≡ vec-len v
vec-len-via-list []V       = refl
vec-len-via-list (x ∷V xs) = cong suc (vec-len-via-list xs)

length-replicate : {A : Set} {a : A} → (n : ℕ) → length (replicate n a) ≡ n
length-replicate 0       = refl
length-replicate (suc n) = cong suc (length-replicate n)

∷-subst : {A : Set} {n m : ℕ} → (x : A) → (xs : Vec A n) → (p : n ≡ m) → x ∷V subst (Vec A) p xs ≡ subst (Vec A) (cong suc p) (x ∷V xs)
∷-subst x xs refl = refl

fromList-toList : {A : Set} {n : ℕ} → (v : Vec A n) → fromList (toList v) ≡ subst (Vec A) (sym (length-toList v)) v
fromList-toList     []V       = refl
fromList-toList {A} (x ∷V xs) = begin
  x ∷V fromList (toList xs)
    ≡⟨ cong (_∷V_ x) (fromList-toList xs) ⟩
  x ∷V subst (Vec A) (sym (length-toList xs)) xs
    ≡⟨ ∷-subst x xs (sym (length-toList xs)) ⟩
  subst (Vec A) (cong suc (sym (length-toList xs))) (x ∷V xs)
    ≡⟨ cong (λ p →  subst (Vec A) p (x ∷V xs)) (proof-irrelevance (cong suc (sym (length-toList xs))) (sym (cong suc (length-toList xs)))) ⟩
  subst (Vec A) (sym (length-toList (x ∷V xs))) (x ∷V xs) ∎

get-commut-2 : (getlen : ℕ → ℕ) → (get : getV-type getlen) → {B : Set} {n : ℕ} → (toList ∘ get {B} {n}) ≗ (getVec-to-getList get) ∘ toList
get-commut-2 getlen get v = {!!}

get-trafo-2-getlen : (getlen : ℕ → ℕ) → (get : getV-type getlen) → proj₁ (getList-to-getVec (getVec-to-getList get)) ≗ getlen
get-trafo-2-getlen getlen get n = begin
  proj₁ (getList-to-getVec (getVec-to-getList get)) n
    ≡⟨ refl ⟩
  length (toList (get (fromList (replicate n tt))))
    ≡⟨ vec-len-via-list (get (fromList (replicate n tt))) ⟩
  vec-len (get (fromList (replicate n tt)))
    ≡⟨ cong getlen (length-replicate n) ⟩
  getlen n ∎

getVec-getlen : {getlen₁ getlen₂ : ℕ → ℕ} → (get : getV-type getlen₁) → getlen₁ ≗ getlen₂ → getV-type getlen₂
getVec-getlen get p {B} {n} v = subst (Vec B) (p n) (get v)

get-trafo-2-get : (getlen : ℕ → ℕ) → (get : getV-type getlen) → {B : Set} {n : ℕ} → proj₂ (getList-to-getVec (getVec-to-getList get)) {B} {n} ≗ getVec-getlen get (sym ∘ (get-trafo-2-getlen getlen get))
get-trafo-2-get getlen get {B} v = begin
  proj₂ (getList-to-getVec (getVec-to-getList get)) v
    ≡⟨ refl ⟩
  subst (Vec B) (getList-to-getVec-length-property (getVec-to-getList get) v) (fromList (toList (get (fromList (toList v)))))
    ≡⟨ {!!} ⟩
  subst (Vec B) (sym (get-trafo-2-getlen getlen get (vec-len v))) (subst (Vec B) (cong getlen (length-toList v)) (get (fromList (toList v))))
    ≡⟨ {!!} ⟩
  subst (Vec B) (sym (get-trafo-2-getlen getlen get (vec-len v))) (get v)
    ≡⟨ refl ⟩
  getVec-getlen get (sym ∘ (get-trafo-2-getlen getlen get)) v ∎
