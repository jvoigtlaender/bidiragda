module LiftGet where

open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; suc)
open import Data.Vec using (Vec ; toList ; fromList) renaming ([] to []V ; _∷_ to _∷V_ ; map to mapV)
open import Data.List using (List ; [] ; _∷_ ; length ; replicate ; map)
open import Data.List.Properties using (length-map)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Function using (_∘_ ; flip ; const)
open import Relation.Binary.Core using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≗_ ; sym ; cong ; refl ; subst ; trans ; proof-irrelevance)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

import FreeTheorems
open import Generic using (length-replicate ; subst-cong ; subst-fromList ; subst-subst ; toList-fromList ; toList-subst)
open FreeTheorems.ListList using (get-type) renaming (free-theorem to free-theoremL ; Get to GetL ; module Get to GetL)
open FreeTheorems.VecVec using () renaming (get-type to getV-type ; Get to GetV ; module Get to GetV)

getVec-to-getList : {getlen : ℕ → ℕ} → (getV-type getlen) → get-type
getVec-to-getList get = toList ∘ get ∘ fromList

fromList∘map : {α β : Set} → (f : α → β) → (l : List α) → fromList (map f l) ≡ subst (Vec β) (sym (length-map f l)) (mapV f (fromList l))
fromList∘map f []       = refl
fromList∘map f (x ∷ xs) rewrite fromList∘map f xs = trans (subst-cong (Vec _) (_∷V_ (f x)) (sym (length-map f xs)) (mapV f (fromList xs)))
                                                          (cong (flip (subst (Vec _)) (f x ∷V mapV f (fromList xs))) (proof-irrelevance (cong suc (sym (length-map f xs)))
                                                                                                                                        (sym (cong suc (length-map f xs)))))

toList∘map : {α β : Set} {n : ℕ} → (f : α → β) → (v : Vec α n) → toList (mapV f v) ≡ map f (toList v)
toList∘map f []V       = refl
toList∘map f (x ∷V xs) = cong (_∷_ (f x)) (toList∘map f xs)

GetV-to-GetL : GetV → GetL
GetV-to-GetL getrecord = record { get = toList ∘ get ∘ fromList; free-theorem = ft }
  where open GetV getrecord
        ft : {α β : Set} → (f : α → β) → (xs : List α) → toList (get (fromList (map f xs))) ≡ map f (toList (get (fromList xs)))
        ft f xs = begin
          toList (get (fromList (map f xs)))
            ≡⟨ cong (toList ∘ get) (fromList∘map f xs) ⟩
          toList (get (subst (Vec _) (sym (length-map f xs)) (mapV f (fromList xs))))
            ≡⟨ cong toList (subst-cong (Vec _) get (sym (length-map f xs)) (mapV f (fromList xs))) ⟩
          toList (subst (Vec _) (cong getlen (sym (length-map f xs))) (get (mapV f (fromList xs))))
            ≡⟨ toList-subst (get (mapV f (fromList xs))) (cong getlen (sym (length-map f xs))) ⟩
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

getList-to-getVec : get-type → ∃ λ (getlen : ℕ → ℕ) → (getV-type getlen)
getList-to-getVec get = getlen , get'
  where getlen : ℕ → ℕ
        getlen = getList-to-getlen get
        get' : {C : Set} {m : ℕ} → Vec C m → Vec C (getlen m)
        get' {C} v = subst (Vec C) (getList-to-getVec-length-property get v) (fromList (get (toList v)))

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

get-trafo-2-get : (getlen : ℕ → ℕ) → (get : getV-type getlen) → {B : Set} {n : ℕ} → proj₂ (getList-to-getVec (getVec-to-getList get)) ≗ subst (Vec B) (sym (get-trafo-2-getlen getlen get n)) ∘ get
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
  subst (Vec B) p'' (get v) ∎
    where n' : ℕ
          n' = length (toList (get (fromList (replicate n tt))))
          p : length (toList (get (fromList (toList v)))) ≡ n'
          p = getList-to-getVec-length-property (getVec-to-getList get) v
          p' : getlen (length (toList v)) ≡ length (toList (get (fromList (toList v))))
          p' = sym (length-toList (get (fromList (toList v))))
          p'' : getlen n ≡ n'
          p'' = sym (get-trafo-2-getlen getlen get (vec-len v))
