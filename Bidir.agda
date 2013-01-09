open import Relation.Binary.Core using (Decidable ; _≡_)

module Bidir (Carrier : Set) (deq : Decidable {A = Carrier} _≡_) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Props using (_≟_)
open import Data.Maybe using (Maybe ; nothing ; just ; maybe′)
open import Data.List using (List)
open import Data.List.Any using (Any ; any ; here ; there)
open import Data.List.All using (All)
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)
open import Data.Vec using (Vec ; [] ; _∷_ ; toList ; fromList ; map ; tabulate) renaming (lookup to lookupVec)
open import Data.Vec.Properties using (tabulate-∘ ; lookup∘tabulate ; map-cong ; map-∘)
open import Data.Product using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (id ; _∘_ ; flip)
open import Relation.Nullary using (yes ; no)
open import Relation.Binary.Core using (refl)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; [_] ; _≗_ ; trans ; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

import FreeTheorems
open FreeTheorems.VecVec using (get-type ; free-theorem)
open import FinMap
import CheckInsert
open CheckInsert Carrier deq
open import BFF using (_>>=_ ; fmap)
open BFF.VecBFF Carrier deq using (assoc ; enumerate ; denumerate ; bff)

lemma-1 : {m n : ℕ} → (f : Fin n → Carrier) → (is : Vec (Fin n) m) → assoc is (map f is) ≡ just (restrict f (toList is))
lemma-1 f []        = refl
lemma-1 f (i ∷ is′) = begin
  assoc is′ (map f is′) >>= checkInsert i (f i)
    ≡⟨ cong (λ m → m >>= checkInsert i (f i)) (lemma-1 f is′) ⟩
  checkInsert i (f i) (restrict f (toList is′))
    ≡⟨ lemma-checkInsert-restrict f i (toList is′) ⟩
  just (restrict f (toList (i ∷ is′))) ∎

lemma-lookupM-assoc : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (x : Carrier) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc (i ∷ is) (x ∷ xs) ≡ just h → lookupM i h ≡ just x
lemma-lookupM-assoc i is x xs h    p with assoc is xs
lemma-lookupM-assoc i is x xs h    () | nothing
lemma-lookupM-assoc i is x xs h    p | just h' = apply-checkInsertProof i x h' record
  { same  = λ lookupM≡justx → begin
      lookupM i h
        ≡⟨ cong (lookupM i) (just-injective (trans (sym p) (lemma-checkInsert-same i x h' lookupM≡justx))) ⟩
      lookupM i h'
        ≡⟨ lookupM≡justx ⟩
      just x ∎
  ; new   = λ lookupM≡nothing → begin
      lookupM i h
        ≡⟨ cong (lookupM i) (just-injective (trans (sym p) (lemma-checkInsert-new i x h' lookupM≡nothing))) ⟩
      lookupM i (insert i x h')
        ≡⟨ lemma-lookupM-insert i x h' ⟩
      just x ∎
  ; wrong = λ x' x≢x' lookupM≡justx' → lemma-just≢nothing (trans (sym p) (lemma-checkInsert-wrong i x h' x' x≢x' lookupM≡justx'))
  }

lemma-∉-lookupM-assoc : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc is xs ≡ just h → (i ∉ toList is) → lookupM i h ≡ nothing
lemma-∉-lookupM-assoc i []         []         .empty refl i∉is = lemma-lookupM-empty i
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') h ph i∉is with assoc is' xs' | inspect (assoc is') xs'
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') h () i∉is | nothing | [ ph' ]
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') h ph i∉is | just h' | [ ph' ] = begin
  lookupM i h
    ≡⟨ sym (lemma-checkInsert-lookupM i i' (i∉is ∘ here) x' (lookupVec i h) h' h refl ph) ⟩
  lookupM i h'
    ≡⟨ lemma-∉-lookupM-assoc i is' xs' h' ph' (i∉is ∘ there) ⟩
  nothing ∎

_in-domain-of_ : {n : ℕ} {A : Set} → (is : List (Fin n)) → (FinMapMaybe n A) → Set
_in-domain-of_ is h = All (λ i → ∃ λ x → lookupM i h ≡ just x) is

lemma-assoc-domain : {m n : ℕ} → (is : Vec (Fin n) m) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc is xs ≡ just h → (toList is) in-domain-of h
lemma-assoc-domain []         []         h ph = Data.List.All.[]
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h ph with assoc is' xs' | inspect (assoc is') xs'
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h () | nothing | [ ph' ]
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h ph | just h' | [ ph' ] = apply-checkInsertProof i' x' h' record {
    same = λ lookupM-i'-h'≡just-x' → Data.List.All._∷_
      (x' , (trans (cong (lookupM i') (just-injective (trans (sym ph) (lemma-checkInsert-same i' x' h' lookupM-i'-h'≡just-x')))) lookupM-i'-h'≡just-x'))
      (lemma-assoc-domain is' xs' h (trans ph' (trans (sym (lemma-checkInsert-same i' x' h' lookupM-i'-h'≡just-x')) ph)))
  ; new  = λ lookupM-i'-h'≡nothing → Data.List.All._∷_
      (x' , (trans (cong (lookupM i') (just-injective (trans (sym ph) (lemma-checkInsert-new i' x' h' lookupM-i'-h'≡nothing)))) (lemma-lookupM-insert i' x' h')))
      (Data.List.All.map
        (λ {i} p → proj₁ p , lemma-lookupM-checkInsert i i' (proj₁ p) x' h' h (proj₂ p) ph)
        (lemma-assoc-domain is' xs' h' ph'))
  ; wrong = λ x'' x'≢x'' lookupM-i'-h'≡just-x'' → lemma-just≢nothing (trans (sym ph) (lemma-checkInsert-wrong i' x' h' x'' x'≢x'' lookupM-i'-h'≡just-x''))
  }

lemma-map-lookupM-insert : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (x : Carrier) → (h : FinMapMaybe n Carrier) → i ∉ (toList is) → map (flip lookupM (insert i x h)) is ≡ map (flip lookupM h) is
lemma-map-lookupM-insert i []         x h i∉is = refl
lemma-map-lookupM-insert i (i' ∷ is') x h i∉is = cong₂ _∷_
  (sym (lemma-lookupM-insert-other i' i x h (i∉is ∘ here ∘ sym)))
  (lemma-map-lookupM-insert i is' x h (i∉is ∘ there))

lemma-map-lookupM-assoc : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (x : Carrier) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → (h' : FinMapMaybe n Carrier) → assoc is xs ≡ just h' → checkInsert i x h' ≡ just h → map (flip lookupM h) is ≡ map (flip lookupM h') is
lemma-map-lookupM-assoc i is x xs h h' ph' ph with any (_≟_ i) (toList is)
lemma-map-lookupM-assoc i is x xs h h' ph' ph | yes p with Data.List.All.lookup (lemma-assoc-domain is xs h' ph') p
lemma-map-lookupM-assoc i is x xs h h' ph' ph | yes p | (x'' , p') with lookupM i h' 
lemma-map-lookupM-assoc i is x xs h h' ph' ph | yes p | (x'' , refl) | .(just x'') with deq x x''
lemma-map-lookupM-assoc i is x xs h .h ph' refl | yes p | (.x , refl) | .(just x)  | yes refl = refl
lemma-map-lookupM-assoc i is x xs h h' ph' () | yes p | (x'' , refl) | .(just x'') | no ¬p
lemma-map-lookupM-assoc i is x xs h h' ph' ph | no ¬p rewrite lemma-∉-lookupM-assoc i is xs h' ph' ¬p = begin
  map (flip lookupM h) is
    ≡⟨ map-cong (λ i'' → cong (lookupM i'') (just-injective (sym ph))) is ⟩
  map (flip lookupM (insert i x h')) is
    ≡⟨ lemma-map-lookupM-insert i is x h' ¬p ⟩
  map (flip lookupM h') is ∎

lemma-2 : {m n : ℕ} → (is : Vec (Fin n) m) → (v : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc is v ≡ just h → map (flip lookupM h) is ≡ map just v
lemma-2 []       []       h p = refl
lemma-2 (i ∷ is) (x ∷ xs) h p with assoc is xs | inspect (assoc is) xs
lemma-2 (i ∷ is) (x ∷ xs) h () | nothing | _
lemma-2 (i ∷ is) (x ∷ xs) h p | just h' | [ ir ] = begin
  lookupM i h ∷ map (flip lookupM h) is
    ≡⟨ cong (flip _∷_ (map (flip lookupM h) is)) (lemma-lookupM-assoc i is x xs h (begin
      assoc (i ∷ is) (x ∷ xs)
        ≡⟨ cong (flip _>>=_ (checkInsert i x)) ir ⟩
      checkInsert i x h'
        ≡⟨ p ⟩
      just h ∎) ) ⟩
  just x ∷ map (flip lookupM h) is
    ≡⟨  cong (_∷_ (just x)) (lemma-map-lookupM-assoc i is x xs h h' ir p) ⟩
  just x ∷ map (flip lookupM h') is
    ≡⟨ cong (_∷_ (just x)) (lemma-2 is xs h' ir) ⟩
  just x ∷ map just xs ∎

lemma-map-denumerate-enumerate : {m : ℕ} → (as : Vec Carrier m) → map (denumerate as) (enumerate as) ≡ as
lemma-map-denumerate-enumerate []       = refl
lemma-map-denumerate-enumerate (a ∷ as) = cong (_∷_ a) (begin
  map (flip lookupVec (a ∷ as)) (tabulate Fin.suc)
    ≡⟨ cong (map (flip lookupVec (a ∷ as))) (tabulate-∘ Fin.suc id) ⟩
  map (flip lookupVec (a ∷ as)) (map Fin.suc (tabulate id))
    ≡⟨ refl ⟩
  map (flip lookupVec (a ∷ as)) (map Fin.suc (enumerate as))
    ≡⟨ sym (map-∘ _ _ (enumerate as)) ⟩
  map (flip lookupVec (a ∷ as) ∘ Fin.suc) (enumerate as)
    ≡⟨ refl ⟩
  map (denumerate as) (enumerate as)
    ≡⟨ lemma-map-denumerate-enumerate as ⟩
  as ∎)

theorem-1 : {getlen : ℕ → ℕ} → (get : get-type getlen) → {m : ℕ} → (s : Vec Carrier m) → bff get s (get s) ≡ just s
theorem-1 get s = begin
  bff get s (get s)
    ≡⟨ cong (bff get s ∘ get) (sym (lemma-map-denumerate-enumerate s)) ⟩
  bff get s (get (map (denumerate s) (enumerate s)))
    ≡⟨ cong (bff get s) (free-theorem get (denumerate s) (enumerate s)) ⟩
  bff get s (map (denumerate s) (get (enumerate s)))
    ≡⟨ refl ⟩
  (h′↦r ∘ h↦h′) (assoc (get (enumerate s)) (map (denumerate s) (get (enumerate s))))
    ≡⟨ cong (h′↦r ∘ h↦h′) (lemma-1 (denumerate s) (get (enumerate s))) ⟩
  (h′↦r ∘ h↦h′ ∘ just) (restrict (denumerate s) (toList (get (enumerate s))))
    ≡⟨ refl ⟩
  (h′↦r ∘ just) (union (restrict (denumerate s) (toList (get (enumerate s)))) (fromFunc (denumerate s)))
    ≡⟨ cong (h′↦r ∘ just) (lemma-union-restrict (denumerate s) (toList (get (enumerate s)))) ⟩
  (h′↦r ∘ just) (fromFunc (denumerate s))
    ≡⟨ refl ⟩
  just (map (flip lookup (fromFunc (denumerate s))) (enumerate s))
    ≡⟨ cong just (map-cong (lookup∘tabulate (denumerate s)) (enumerate s)) ⟩
  just (map (denumerate s) (enumerate s))
    ≡⟨ cong just (lemma-map-denumerate-enumerate s) ⟩
  just s ∎
    where h↦h′ = fmap (flip union (fromFunc (denumerate s)))
          h′↦r = fmap (flip map (enumerate s) ∘ flip lookupVec)

lemma-fmap-just : {A B : Set} {f : A → B} {b : B} {ma : Maybe A} → fmap f ma ≡ just b → ∃ λ a → ma ≡ just a
lemma-fmap-just {ma = just x}  fmap-f-ma≡just-b = x , refl
lemma-fmap-just {ma = nothing} ()

∷-injective : {A : Set} {n : ℕ} {x y : A} {xs ys : Vec A n} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

map-just-injective : {A : Set} {n : ℕ} {xs ys : Vec A n} → map Maybe.just xs ≡ map Maybe.just ys → xs ≡ ys
map-just-injective {xs = []}      {ys = []}       p  = refl
map-just-injective {xs = x ∷ xs'} {ys = y ∷ ys'}  p with ∷-injective p
map-just-injective {xs = x ∷ xs'} {ys = .x ∷ ys'} p | refl , p' = cong (_∷_ x) (map-just-injective p')

lemma-union-not-used : {m n : ℕ} {A : Set} (h : FinMapMaybe n A) → (h' : FinMap n A) → (is : Vec (Fin n) m) → (toList is) in-domain-of h → map just (map (flip lookup (union h h')) is) ≡ map (flip lookupM h) is
lemma-union-not-used h h' []        p = refl
lemma-union-not-used h h' (i ∷ is') p with Data.List.All.head p
lemma-union-not-used h h' (i ∷ is') p | x , lookupM-i-h≡just-x = cong₂ _∷_ (begin
      just (lookup i (union h h'))
        ≡⟨ cong just (lookup∘tabulate (λ j → maybe′ id (lookup j h') (lookupM j h)) i) ⟩
      just (maybe′ id (lookup i h') (lookupM i h))
        ≡⟨ cong just (cong (maybe′ id (lookup i h')) lookupM-i-h≡just-x) ⟩
      just (maybe′ id (lookup i h') (just x))
        ≡⟨ refl ⟩
      just x
        ≡⟨ sym lookupM-i-h≡just-x ⟩
      lookupM i h ∎)
  (lemma-union-not-used h h' is' (Data.List.All.tail p))

theorem-2 : {getlen : ℕ → ℕ} (get : get-type getlen) → {m : ℕ} → (v : Vec Carrier (getlen m)) → (s u : Vec Carrier m) → bff get s v ≡ just u → get u ≡ v
theorem-2 get v s u p with lemma-fmap-just (proj₂ (lemma-fmap-just p))
theorem-2 get v s u p | h , ph = begin
  get u
    ≡⟨ just-injective (begin
      fmap get (just u)
        ≡⟨ cong (fmap get) (sym p) ⟩
      fmap get (bff get s v)
        ≡⟨ cong (fmap get ∘ fmap h′↦r ∘ fmap h↦h′) ph ⟩
      fmap get (fmap h′↦r (fmap h↦h′ (just h))) ∎) ⟩
  get (map (flip lookup (h↦h′ h)) s′)
    ≡⟨ free-theorem get (flip lookup (h↦h′ h)) s′ ⟩
  map (flip lookup (h↦h′ h)) (get s′)
     ≡⟨ map-just-injective (begin
       map just (map (flip lookup (union h g)) (get s′))
         ≡⟨ lemma-union-not-used h g (get s′) (lemma-assoc-domain (get s′) v h ph) ⟩
       map (flip lookupM h) (get s′)
         ≡⟨ lemma-2 (get s′) v h ph ⟩
       map just v
         ∎) ⟩
  v ∎
    where s′   = enumerate s
          g    = fromFunc (denumerate s)
          h↦h′ = flip union g
          h′↦r = flip map s′ ∘ flip lookupVec
