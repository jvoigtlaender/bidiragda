module LiftGet where

open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; suc)
open import Data.Vec using (Vec ; toList ; fromList) renaming ([] to []V ; _∷_ to _∷V_ ; map to mapV)
open import Data.List using (List ; [] ; _∷_ ; length ; replicate ; map)
open import Data.List.Properties using (length-map)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Function using (_∘_ ; flip ; const)
open import Relation.Binary.Core using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≗_ ; sym ; cong ; refl ; subst ; trans ; proof-irrelevance ; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality as H using (module ≅-Reasoning ; _≅_ ; ≅-to-≡ ; ≡-to-≅ ; ≡-subst-removable) renaming (refl to het-refl ; sym to het-sym ; cong to het-cong ; reflexive to het-reflexive)

import FreeTheorems
open import Generic using (length-replicate ; toList-fromList ; toList-subst)
open FreeTheorems.ListList using (get-type) renaming (free-theorem to free-theoremL ; Get to GetL ; module Get to GetL)
open FreeTheorems.VecVec using () renaming (get-type to getV-type ; Get to GetV ; module Get to GetV)

getVec-to-getList : {getlen : ℕ → ℕ} → (getV-type getlen) → get-type
getVec-to-getList get = toList ∘ get ∘ fromList

fromList∘map : {α β : Set} → (f : α → β) → (l : List α) → fromList (map f l) ≅ mapV f (fromList l)
fromList∘map f []       = het-refl
fromList∘map f (x ∷ xs) = H.cong₂ (λ n → _∷V_ {n = n} (f x)) (H.reflexive (length-map f xs)) (fromList∘map f xs)

toList∘map : {α β : Set} {n : ℕ} → (f : α → β) → (v : Vec α n) → toList (mapV f v) ≡ map f (toList v)
toList∘map f []V       = refl
toList∘map f (x ∷V xs) = cong (_∷_ (f x)) (toList∘map f xs)

GetV-to-GetL : GetV → GetL
GetV-to-GetL getrecord = record { get = toList ∘ get ∘ fromList; free-theorem = ft }
  where open GetV getrecord
        open ≡-Reasoning
        ft : {α β : Set} → (f : α → β) → (xs : List α) → toList (get (fromList (map f xs))) ≡ map f (toList (get (fromList xs)))
        ft f xs = begin
          toList (get (fromList (map f xs)))
            ≅⟨ H.cong₂ {B = Vec _} (λ n → toList ∘ get) (het-reflexive (length-map f xs)) (fromList∘map f xs) ⟩
          toList (get (mapV f (fromList xs)))
            ≡⟨ cong toList (free-theorem f (fromList xs)) ⟩
          toList (mapV f (get (fromList xs)))
            ≡⟨ toList∘map f (get (fromList xs)) ⟩
          map f (toList (get (fromList xs))) ∎

getList-to-getlen : get-type → ℕ → ℕ
getList-to-getlen get = length ∘ get ∘ flip replicate tt

replicate-length : {A : Set} → (l : List A) → map (const tt) l ≡ replicate (length l) tt
replicate-length [] = refl
replicate-length (_ ∷ l) = cong (_∷_ tt) (replicate-length l)

getList-length : (get : get-type) → {B : Set} → (l : List B) → length (get l) ≡ getList-to-getlen get (length l)
getList-length get l = begin
  length (get l)
    ≡⟨ sym (length-map (const tt) (get l)) ⟩
  length (map (const tt) (get l))
    ≡⟨ cong length (sym (free-theoremL get (const tt) l)) ⟩
  length (get (map (const tt) l))
    ≡⟨ cong (length ∘ get) (replicate-length l) ⟩
  length (get (replicate (length l) tt)) ∎
  where open ≡-Reasoning

length-toList : {A : Set} {n : ℕ} → (v : Vec A n) → length (toList v) ≡ n
length-toList []V = refl
length-toList (x ∷V xs) = cong suc (length-toList xs) 

getList-to-getVec-length-property : (get : get-type) → {C : Set} → {m : ℕ} → (v : Vec C m) → length (get (toList v)) ≡ length (get (replicate m tt))
getList-to-getVec-length-property get {_} {m} v = begin
    length (get (toList v))
      ≡⟨ getList-length get (toList v) ⟩
    length (get (replicate (length (toList v)) tt))
      ≡⟨ cong (length ∘ get ∘ flip replicate tt) (length-toList v) ⟩
    length (get (replicate m tt)) ∎
    where open ≡-Reasoning

getList-to-getVec : get-type → ∃ λ (getlen : ℕ → ℕ) → (getV-type getlen)
getList-to-getVec get = getlen , get'
  where getlen : ℕ → ℕ
        getlen = getList-to-getlen get
        get' : {C : Set} {m : ℕ} → Vec C m → Vec C (getlen m)
        get' {C} v = subst (Vec C) (getList-to-getVec-length-property get v) (fromList (get (toList v)))

private
  module GetV-Implementation (getrecord : GetL) where

    open GetL getrecord

    getlen = length ∘ get ∘ flip replicate tt


    length-property : {C : Set} {m : ℕ} → (s : Vec C m) → length (get (toList s)) ≡ getlen m
    length-property = getList-to-getVec-length-property get

    getV : {C : Set} {m : ℕ} → Vec C m → Vec C (getlen m)
    getV s = subst (Vec _) (length-property s) (fromList (get (toList s)))

    ft : {α β : Set} (f : α → β) {n : ℕ} (v : Vec α n) → getV (mapV f v) ≡ mapV f (getV v)
    ft f v = ≅-to-≡ (begin
      subst (Vec _) (length-property (mapV f v)) (fromList (get (toList (mapV f v))))
        ≅⟨ ≡-subst-removable (Vec _) (length-property (mapV f v)) (fromList (get (toList (mapV f v)))) ⟩
      fromList (get (toList (mapV f v)))
        ≅⟨ het-cong (fromList ∘ get) (het-reflexive (toList∘map f v)) ⟩
      fromList (get (map f (toList v)))
        ≅⟨ het-cong fromList (het-reflexive (free-theorem f (toList v))) ⟩
      fromList (map f (get (toList v)))
        ≅⟨ fromList∘map f (get (toList v)) ⟩
      mapV f (fromList (get (toList v)))
        ≅⟨ H.cong₂ (λ n → mapV {n = n} f) (H.reflexive (length-property v)) (H.sym (≡-subst-removable (Vec _) (length-property v) (fromList (get (toList v))))) ⟩
      mapV f (subst (Vec _) (length-property v) (fromList (get (toList v)))) ∎)
      where open ≅-Reasoning

GetL-to-GetV : GetL → GetV
GetL-to-GetV getrecord = record { getlen = getlen; get = getV; free-theorem = ft }
  where open GetV-Implementation getrecord

get-commut-1-≅ : (get : get-type) {A : Set} → (l : List A) → fromList (get l) ≅ proj₂ (getList-to-getVec get) (fromList l)
get-commut-1-≅ get l = begin
  fromList (get l)
    ≅⟨ het-cong (fromList ∘ get) (≡-to-≅ (sym (toList-fromList l))) ⟩
  fromList (get (toList (fromList l)))
    ≅⟨ het-sym (≡-subst-removable (Vec _) (getList-to-getVec-length-property get (fromList l)) (fromList (get (toList (fromList l))))) ⟩
  subst (Vec _) (getList-to-getVec-length-property get (fromList l)) (fromList (get (toList (fromList l)))) ∎
  where open ≅-Reasoning

get-commut-1 : (get : get-type) {A : Set} → (l : List A) → fromList (get l) ≡ subst (Vec A) (sym (getList-length get l)) (proj₂ (getList-to-getVec get) (fromList l))
get-commut-1 get {A} l = ≅-to-≡ (begin
  fromList (get l)
    ≅⟨ get-commut-1-≅ get l ⟩
  proj₂ (getList-to-getVec get) (fromList l)
    ≅⟨ het-sym (≡-subst-removable (Vec _) (sym (getList-length get l)) (proj₂ (getList-to-getVec get) (fromList l))) ⟩
  subst (Vec _) (sym (getList-length get l)) (proj₂ (getList-to-getVec get) (fromList l)) ∎)
  where open ≅-Reasoning

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
  where open ≡-Reasoning

GetLVL-identity : (G : GetL) → {A : Set} → GetL.get (GetV-to-GetL (GetL-to-GetV G)) ≗ GetL.get G {A}
GetLVL-identity G = get-trafo-1 (GetL.get G)

vec-len : {A : Set} {n : ℕ} → Vec A n → ℕ
vec-len {_} {n} _ = n

fromList-toList : {A : Set} {n : ℕ} → (v : Vec A n) → fromList (toList v) ≅ v
fromList-toList []V       = het-refl
fromList-toList (x ∷V xs) = H.cong₂ (λ n → _∷V_ {n = n} x) (het-reflexive (length-toList xs)) (fromList-toList xs)

get-commut-2 : {getlen : ℕ → ℕ} → (get : getV-type getlen) → {B : Set} {n : ℕ} → (toList ∘ get {B} {n}) ≗ (getVec-to-getList get) ∘ toList
get-commut-2 get {B} v = sym (≅-to-≡ (H.cong₂ (λ n → toList ∘ get {n = n}) (H.reflexive (length-toList v)) (fromList-toList v)))

get-trafo-2-getlen : {getlen : ℕ → ℕ} → (get : getV-type getlen) → proj₁ (getList-to-getVec (getVec-to-getList get)) ≗ getlen
get-trafo-2-getlen {getlen} get n = begin
  proj₁ (getList-to-getVec (getVec-to-getList get)) n
    ≡⟨ refl ⟩
  length (toList (get (fromList (replicate n tt))))
    ≡⟨ length-toList (get (fromList (replicate n tt))) ⟩
  vec-len (get (fromList (replicate n tt)))
    ≡⟨ cong getlen (length-replicate n) ⟩
  getlen n ∎
  where open ≡-Reasoning

get-trafo-2-get-≅ : {getlen : ℕ → ℕ} → (get : getV-type getlen) → {B : Set} {n : ℕ} → (v : Vec B n) → proj₂ (getList-to-getVec (getVec-to-getList get)) v ≅ get v
get-trafo-2-get-≅ {getlen} get v = begin
  subst (Vec _) (getList-to-getVec-length-property (getVec-to-getList get) v) (fromList (toList (get (fromList (toList v)))))
    ≅⟨ ≡-subst-removable (Vec _) (getList-to-getVec-length-property (getVec-to-getList get) v) (fromList (toList (get (fromList (toList v))))) ⟩
  fromList (toList (get (fromList (toList v))))
    ≅⟨ fromList-toList (get (fromList (toList v))) ⟩
  get (fromList (toList v))
    ≅⟨ H.cong₂ (λ n → get {n = n}) (H.reflexive (length-toList v)) (fromList-toList v) ⟩
  get v ∎
  where open ≅-Reasoning

get-trafo-2-get : {getlen : ℕ → ℕ} → (get : getV-type getlen) → {B : Set} {n : ℕ} → proj₂ (getList-to-getVec (getVec-to-getList get)) ≗ subst (Vec B) (sym (get-trafo-2-getlen get n)) ∘ get
get-trafo-2-get get v = ≅-to-≡ (begin
  proj₂ (getList-to-getVec (getVec-to-getList get)) v
    ≅⟨ get-trafo-2-get-≅ get v ⟩
  get v
    ≅⟨ het-sym (≡-subst-removable (Vec _) (sym (get-trafo-2-getlen get (vec-len v))) (get v)) ⟩
  subst (Vec _) (sym (get-trafo-2-getlen get (vec-len v))) (get v) ∎)
  where open ≅-Reasoning
