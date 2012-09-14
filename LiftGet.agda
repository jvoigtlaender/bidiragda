module LiftGet where

open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; suc)
open import Data.Vec using (Vec ; toList ; fromList) renaming ([] to []V ; _∷_ to _∷V_)
open import Data.List using (List ; [] ; _∷_ ; length ; replicate ; map)
open import Data.List.Properties using (length-map)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Function using (_∘_ ; flip ; const)
open import Relation.Binary.Core using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≗_ ; sym ; cong ; refl ; subst ; trans ; proof-irrelevance)
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

subst-subst : {A : Set} (T : A → Set) {a b c : A} → (p : a ≡ b) → (p' : b ≡ c) → (x : T a)→ subst T p' (subst T p x) ≡ subst T (trans p p') x
subst-subst T refl p' x = refl

subst-fromList : {A : Set} {x y : List A} → (p : y ≡ x) → subst (Vec A) (cong length p) (fromList y) ≡ fromList x
subst-fromList refl = refl

get-commut-1 : (get : get-type) {A : Set} → (l : List A) → fromList (get l) ≡ subst (Vec A) (sym (getList-length get l)) (proj₂ (getList-to-getVec get) (fromList l))
get-commut-1 get {A} l = begin
  fromList (get l)
    ≡⟨ sym (subst-fromList (cong get (toList-fromList l))) ⟩
  subst (Vec A) (cong length (cong get (toList-fromList l))) (fromList (get (toList (fromList l))))
    ≡⟨ cong (flip (subst (Vec A)) (fromList (get (toList (fromList l))))) (proof-irrelevance (cong length (cong get (toList-fromList l))) (trans p p')) ⟩
  subst (Vec A) (trans p p') (fromList (get (toList (fromList l))))
    ≡⟨ sym (subst-subst (Vec A) p p' (fromList (get (toList (fromList l))))) ⟩
  subst (Vec A) p' (subst (Vec A) p (fromList (get (toList (fromList l)))))
    ≡⟨ refl ⟩
  subst (Vec A) p' (proj₂ (getList-to-getVec get) (fromList l)) ∎
    where p : length (get (toList (fromList l))) ≡ length (get (replicate (length l) tt))
          p = getList-to-getVec-length-property get (fromList l)
          p' : length (get (replicate (length l) tt)) ≡ length (get l)
          p' = sym (getList-length get l)

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

length-replicate : {A : Set} {a : A} → (n : ℕ) → length (replicate n a) ≡ n
length-replicate 0       = refl
length-replicate (suc n) = cong suc (length-replicate n)

subst-cong : {A : Set} → (T : A → Set) → {g : A → A} → {a b : A} → (f : {c : A} → T c → T (g c)) → (p : a ≡ b) → f ∘ subst T p ≗ subst T (cong g p) ∘ f
subst-cong T f refl _ = refl

fromList-toList : {A : Set} {n : ℕ} → (v : Vec A n) → fromList (toList v) ≡ subst (Vec A) (sym (length-toList v)) v
fromList-toList     []V       = refl
fromList-toList {A} (x ∷V xs) = begin
  x ∷V fromList (toList xs)
    ≡⟨ cong (_∷V_ x) (fromList-toList xs) ⟩
  x ∷V subst (Vec A) (sym (length-toList xs)) xs
    ≡⟨ subst-cong (Vec A) (_∷V_ x) (sym (length-toList xs)) xs ⟩
  subst (Vec A) (cong suc (sym (length-toList xs))) (x ∷V xs)
    ≡⟨ cong (λ p →  subst (Vec A) p (x ∷V xs)) (proof-irrelevance (cong suc (sym (length-toList xs))) (sym (cong suc (length-toList xs)))) ⟩
  subst (Vec A) (sym (length-toList (x ∷V xs))) (x ∷V xs) ∎

get-commut-2 : (getlen : ℕ → ℕ) → (get : getV-type getlen) → {B : Set} {n : ℕ} → (toList ∘ get {B} {n}) ≗ (getVec-to-getList get) ∘ toList
get-commut-2 getlen get {B} v = begin
  toList (get v)
    ≡⟨ sym (toList-subst (get v) (cong getlen (sym (length-toList v)))) ⟩
  toList (subst (Vec B) (cong getlen (sym (length-toList v))) (get v))
    ≡⟨ cong toList (sym (subst-cong (Vec B) get (sym (length-toList v)) v)) ⟩
  toList (get (subst (Vec B) (sym (length-toList v)) v))
    ≡⟨ cong (toList ∘ get) (sym (fromList-toList v)) ⟩
  toList (get (fromList (toList v))) ∎

get-trafo-2-getlen : (getlen : ℕ → ℕ) → (get : getV-type getlen) → proj₁ (getList-to-getVec (getVec-to-getList get)) ≗ getlen
get-trafo-2-getlen getlen get n = begin
  proj₁ (getList-to-getVec (getVec-to-getList get)) n
    ≡⟨ refl ⟩
  length (toList (get (fromList (replicate n tt))))
    ≡⟨ length-toList (get (fromList (replicate n tt))) ⟩
  vec-len (get (fromList (replicate n tt)))
    ≡⟨ cong getlen (length-replicate n) ⟩
  getlen n ∎

getVec-getlen : {getlen₁ getlen₂ : ℕ → ℕ} → (get : getV-type getlen₁) → getlen₁ ≗ getlen₂ → getV-type getlen₂
getVec-getlen get p {B} {n} v = subst (Vec B) (p n) (get v)

get-trafo-2-get : (getlen : ℕ → ℕ) → (get : getV-type getlen) → {B : Set} {n : ℕ} → proj₂ (getList-to-getVec (getVec-to-getList get)) {B} {n} ≗ getVec-getlen get (sym ∘ (get-trafo-2-getlen getlen get))
get-trafo-2-get getlen get {B} {n} v = begin
  proj₂ (getList-to-getVec (getVec-to-getList get)) v
    ≡⟨ refl ⟩
  subst (Vec B) p (fromList (toList (get (fromList (toList v)))))
    ≡⟨ cong (subst (Vec B) p) (fromList-toList (get (fromList (toList v)))) ⟩
  subst (Vec B) p (subst (Vec B) p' (get (fromList (toList v))))
    ≡⟨ subst-subst (Vec B) p' p (get (fromList (toList v))) ⟩
  subst (Vec B) (trans p' p) (get (fromList (toList v)))
    ≡⟨ cong (subst (Vec B) (trans p' p) ∘ get) (fromList-toList v) ⟩
  subst (Vec B) (trans p' p) (get (subst (Vec B) (sym (length-toList v)) v))
    ≡⟨ cong (subst (Vec B) (trans p' p)) (subst-cong (Vec B) get (sym (length-toList v)) v) ⟩
  subst (Vec B) (trans p' p) (subst (Vec B) (cong getlen (sym (length-toList v))) (get v))
    ≡⟨ subst-subst (Vec B) (cong getlen (sym (length-toList v))) (trans p' p) (get v) ⟩
  subst (Vec B) (trans (cong getlen (sym (length-toList v))) (trans p' p)) (get v)
    ≡⟨ cong (flip (subst (Vec B)) (get v)) (proof-irrelevance (trans (cong getlen (sym (length-toList v))) (trans p' p)) p'') ⟩
  subst (Vec B) p'' (get v)
    ≡⟨ refl ⟩
  getVec-getlen get (sym ∘ (get-trafo-2-getlen getlen get)) v ∎
    where n' : ℕ
          n' = length (toList (get (fromList (replicate n tt))))
          p : length (toList (get (fromList (toList v)))) ≡ n'
          p = getList-to-getVec-length-property (getVec-to-getList get) v
          p' : getlen (length (toList v)) ≡ length (toList (get (fromList (toList v))))
          p' = sym (length-toList (get (fromList (toList v))))
          p'' : getlen n ≡ n'
          p'' = sym (get-trafo-2-getlen getlen get (vec-len v))
