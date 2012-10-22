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
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Core using (refl)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; [_] ; _≗_ ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

import FreeTheorems
open FreeTheorems.VecVec using (get-type ; free-theorem)
open import FinMap
open import CheckInsert
open import BFF using (_>>=_ ; fmap)
open BFF.VecBFF using (assoc ; enumerate ; denumerate ; bff)

lemma-1 : {m n : ℕ} → (f : Fin n → Carrier) → (is : Vec (Fin n) m) → assoc deq is (map f is) ≡ just (restrict f (toList is))
lemma-1 f []        = refl
lemma-1 f (i ∷ is′) = begin
  assoc deq (i ∷ is′) (map f (i ∷ is′))
    ≡⟨ refl ⟩
  assoc deq is′ (map f is′) >>= checkInsert deq i (f i)
    ≡⟨ cong (λ m → m >>= checkInsert deq i (f i)) (lemma-1 f is′) ⟩
  just (restrict f (toList is′)) >>= (checkInsert deq i (f i))
    ≡⟨ refl ⟩
  checkInsert deq i (f i) (restrict f (toList is′))
    ≡⟨ lemma-checkInsert-restrict deq f i (toList is′) ⟩
  just (restrict f (toList (i ∷ is′))) ∎

lemma-lookupM-assoc : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (x : Carrier) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc deq (i ∷ is) (x ∷ xs) ≡ just h → lookupM i h ≡ just x
lemma-lookupM-assoc i is x xs h    p with assoc deq is xs
lemma-lookupM-assoc i is x xs h    () | nothing
lemma-lookupM-assoc i is x xs h    p | just h' = apply-checkInsertProof deq i x h' record
  { same  = λ lookupM≡justx → begin
      lookupM i h
        ≡⟨ cong (lookupM i) (lemma-from-just (trans (sym p) (lemma-checkInsert-same deq i x h' lookupM≡justx))) ⟩
      lookupM i h'
        ≡⟨ lookupM≡justx ⟩
      just x ∎
  ; new   = λ lookupM≡nothing → begin
      lookupM i h
        ≡⟨ cong (lookupM i) (lemma-from-just (trans (sym p) (lemma-checkInsert-new deq i x h' lookupM≡nothing))) ⟩
      lookupM i (insert i x h')
        ≡⟨ lemma-lookupM-insert i x h' ⟩
      just x ∎
  ; wrong = λ x' x≢x' lookupM≡justx' → lemma-just≢nothing (trans (sym p) (lemma-checkInsert-wrong deq i x h' x' x≢x' lookupM≡justx'))
  }

lemma-∉-lookupM-assoc : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc deq is xs ≡ just h → (i ∉ toList is) → lookupM i h ≡ nothing
lemma-∉-lookupM-assoc i []         []         h ph i∉is = begin
  lookupM i h
    ≡⟨ cong (lookupM i) (sym (lemma-from-just ph)) ⟩
  lookupM i empty
    ≡⟨ lemma-lookupM-empty i ⟩
  nothing ∎
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') h ph i∉is with assoc deq is' xs' | inspect (assoc deq is') xs'
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') h () i∉is | nothing | [ ph' ]
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') h ph i∉is | just h' | [ ph' ] = apply-checkInsertProof deq i' x' h' record {
    same = λ lookupM-i'-h'≡just-x' → begin
      lookupM i h
        ≡⟨ cong (lookupM i) (lemma-from-just (trans (sym ph) (lemma-checkInsert-same deq i' x' h' lookupM-i'-h'≡just-x'))) ⟩
      lookupM i h'
        ≡⟨ lemma-∉-lookupM-assoc i is' xs' h' ph' (i∉is ∘ there) ⟩
      nothing ∎
  ; new = λ lookupM-i'-h'≡nothing → begin
      lookupM i h
        ≡⟨ cong (lookupM i)  (lemma-from-just (trans (sym ph) (lemma-checkInsert-new deq i' x' h' lookupM-i'-h'≡nothing))) ⟩
      lookupM i (insert i' x' h')
        ≡⟨ sym (lemma-lookupM-insert-other i i' x' h' (i∉is ∘ here)) ⟩
      lookupM i h'
        ≡⟨ lemma-∉-lookupM-assoc i is' xs' h' ph' (i∉is ∘ there) ⟩
      nothing ∎
  ; wrong = λ x'' x'≢x'' lookupM-i'-h'≡just-x'' → lemma-just≢nothing (trans (sym ph) (lemma-checkInsert-wrong deq i' x' h' x'' x'≢x'' lookupM-i'-h'≡just-x''))
  }

_in-domain-of_ : {n : ℕ} {A : Set} → (is : List (Fin n)) → (FinMapMaybe n A) → Set
_in-domain-of_ is h = All (λ i → ∃ λ x → lookupM i h ≡ just x) is

lemma-assoc-domain : {m n : ℕ} → (is : Vec (Fin n) m) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc deq is xs ≡ just h → (toList is) in-domain-of h
lemma-assoc-domain []         []         h ph = Data.List.All.[]
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h ph with assoc deq is' xs' | inspect (assoc deq is') xs'
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h () | nothing | [ ph' ]
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h ph | just h' | [ ph' ] = apply-checkInsertProof deq i' x' h' record {
    same = λ lookupM-i'-h'≡just-x' → Data.List.All._∷_
      (x' , (trans (cong (lookupM i') (lemma-from-just (trans (sym ph) (lemma-checkInsert-same deq i' x' h' lookupM-i'-h'≡just-x')))) lookupM-i'-h'≡just-x'))
      (lemma-assoc-domain is' xs' h (trans ph' (trans (sym (lemma-checkInsert-same deq i' x' h' lookupM-i'-h'≡just-x')) ph)))
  ; new  = λ lookupM-i'-h'≡nothing → Data.List.All._∷_
      (x' , (trans (cong (lookupM i') (lemma-from-just (trans (sym ph) (lemma-checkInsert-new deq i' x' h' lookupM-i'-h'≡nothing)))) (lemma-lookupM-insert i' x' h')))
      (Data.List.All.map
        (λ {i} p → proj₁ p , lemma-lookupM-checkInsert deq i i' (proj₁ p) x' h' h (proj₂ p) ph)
        (lemma-assoc-domain is' xs' h' ph'))
  ; wrong = λ x'' x'≢x'' lookupM-i'-h'≡just-x'' → lemma-just≢nothing (trans (sym ph) (lemma-checkInsert-wrong deq i' x' h' x'' x'≢x'' lookupM-i'-h'≡just-x''))
  }

lemma-map-lookupM-insert : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (x : Carrier) → (h : FinMapMaybe n Carrier) → i ∉ (toList is) → (toList is) in-domain-of h → map (flip lookupM (insert i x h)) is ≡ map (flip lookupM h) is
lemma-map-lookupM-insert i []         x h i∉is ph = refl
lemma-map-lookupM-insert i (i' ∷ is') x h i∉is ph = begin
  lookupM i' (insert i x h) ∷ map (flip lookupM (insert i x h)) is'
    ≡⟨ cong (flip _∷_ (map (flip lookupM (insert i x h)) is')) (sym (lemma-lookupM-insert-other i' i x h (i∉is ∘ here ∘ sym))) ⟩
  lookupM i' h ∷ map (flip lookupM (insert i x h)) is'
    ≡⟨ cong (_∷_ (lookupM i' h)) (lemma-map-lookupM-insert i is' x h (i∉is ∘ there) (Data.List.All.tail ph)) ⟩
  lookupM i' h ∷ map (flip lookupM h) is' ∎

lemma-map-lookupM-assoc : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (x : Carrier) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → (h' : FinMapMaybe n Carrier) → assoc deq is xs ≡ just h' → checkInsert deq i x h' ≡ just h → map (flip lookupM h) is ≡ map (flip lookupM h') is
lemma-map-lookupM-assoc i []         x []         h h' ph' ph = refl
lemma-map-lookupM-assoc i (i' ∷ is') x (x' ∷ xs') h h' ph' ph with any (_≟_ i) (toList (i' ∷ is'))
lemma-map-lookupM-assoc i (i' ∷ is') x (x' ∷ xs') h h' ph' ph | yes p with Data.List.All.lookup (lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h' ph') p
lemma-map-lookupM-assoc i (i' ∷ is') x (x' ∷ xs') h h' ph' ph | yes p | (x'' , p') with lookupM i h' 
lemma-map-lookupM-assoc i (i' ∷ is') x (x' ∷ xs') h h' ph' ph | yes p | (x'' , refl) | .(just x'') with deq x x''
lemma-map-lookupM-assoc i (i' ∷ is') x (x' ∷ xs') h .h ph' refl | yes p | (.x , refl) | .(just x)  | yes refl = refl
lemma-map-lookupM-assoc i (i' ∷ is') x (x' ∷ xs') h h' ph' () | yes p | (x'' , refl) | .(just x'') | no ¬p
lemma-map-lookupM-assoc i (i' ∷ is') x (x' ∷ xs') h h' ph' ph | no ¬p rewrite lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') h' ph' ¬p = begin
  map (flip lookupM h) (i' ∷ is')
    ≡⟨ map-cong (λ i'' → cong (lookupM i'') (lemma-from-just (sym ph))) (i' ∷ is') ⟩
  map (flip lookupM (insert i x h')) (i' ∷ is')
    ≡⟨ lemma-map-lookupM-insert i (i' ∷ is') x h' ¬p (lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h' ph') ⟩
  map (flip lookupM h') (i' ∷ is') ∎

lemma-2 : {m n : ℕ} → (is : Vec (Fin n) m) → (v : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc deq is v ≡ just h → map (flip lookupM h) is ≡ map just v
lemma-2 []       []       h p = refl
lemma-2 (i ∷ is) (x ∷ xs) h p with assoc deq is xs | inspect (assoc deq is) xs
lemma-2 (i ∷ is) (x ∷ xs) h () | nothing | _
lemma-2 (i ∷ is) (x ∷ xs) h p | just h' | [ ir ] = begin
  map (flip lookupM h) (i ∷ is)
    ≡⟨ refl ⟩
  lookupM i h ∷ map (flip lookupM h) is
    ≡⟨ cong (flip _∷_ (map (flip lookupM h) is)) (lemma-lookupM-assoc i is x xs h (begin
      assoc deq (i ∷ is) (x ∷ xs)
        ≡⟨ cong (flip _>>=_ (checkInsert deq i x)) ir ⟩
      checkInsert deq i x h'
        ≡⟨ p ⟩
      just h ∎) ) ⟩
  just x ∷ map (flip lookupM h) is
    ≡⟨  cong (_∷_ (just x)) (lemma-map-lookupM-assoc i is x xs h h' ir p) ⟩
  just x ∷ map (flip lookupM h') is
    ≡⟨ cong (_∷_ (just x)) (lemma-2 is xs h' ir) ⟩
  just x ∷ map just xs
    ≡⟨ refl ⟩
  map just (x ∷ xs) ∎

lemma-map-denumerate-enumerate : {m : ℕ} {A : Set} → (as : Vec A m) → map (denumerate as) (enumerate as) ≡ as
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

theorem-1 : {getlen : ℕ → ℕ} → (get : get-type getlen) → {m : ℕ} → (s : Vec Carrier m) → bff get deq s (get s) ≡ just s
theorem-1 get s = begin
  bff get deq s (get s)
    ≡⟨ cong (bff get deq s ∘ get) (sym (lemma-map-denumerate-enumerate s)) ⟩
  bff get deq s (get (map (denumerate s) (enumerate s)))
    ≡⟨ cong (bff get deq s) (free-theorem get (denumerate s) (enumerate s)) ⟩
  bff get deq s (map (denumerate s) (get (enumerate s)))
    ≡⟨ refl ⟩
  fmap (flip map (enumerate s) ∘ flip lookup) (fmap (flip union (fromFunc (denumerate s))) (assoc deq (get (enumerate s)) (map (denumerate s) (get (enumerate s)))))
    ≡⟨ cong (fmap (flip map (enumerate s) ∘ flip lookup) ∘ fmap (flip union (fromFunc (denumerate s)))) (lemma-1 (denumerate s) (get (enumerate s))) ⟩
  fmap (flip map (enumerate s) ∘ flip lookup) (fmap (flip union (fromFunc (flip lookupVec s))) (just (restrict (denumerate s) (toList (get (enumerate s))))))
    ≡⟨ refl ⟩
  just ((flip map (enumerate s) ∘ flip lookup) (union (restrict (denumerate s) (toList (get (enumerate s)))) (fromFunc (denumerate s))))
    ≡⟨ cong just (cong (flip map (enumerate s) ∘ flip lookup) (lemma-union-restrict (denumerate s) (toList (get (enumerate s))))) ⟩
  just ((flip map (enumerate s) ∘ flip lookup) (fromFunc (denumerate s)))
    ≡⟨ refl ⟩
  just (map (flip lookup (fromFunc (denumerate s))) (enumerate s))
    ≡⟨ cong just (map-cong (lookup∘tabulate (denumerate s)) (enumerate s)) ⟩
  just (map (denumerate s) (enumerate s))
    ≡⟨ cong just (lemma-map-denumerate-enumerate s) ⟩
  just s ∎

lemma-fmap-just : {A B : Set} → {f : A → B} {b : B} → (ma : Maybe A) → fmap f ma ≡ just b → ∃ λ a → ma ≡ just a
lemma-fmap-just (just x) fmap-f-ma≡just-b = x , refl
lemma-fmap-just nothing  ()

∷-injective : {A : Set} {n : ℕ} {x y : A} {xs ys : Vec A n} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

lemma-from-map-just : {A : Set} {n : ℕ} → {xs ys : Vec A n} → map Maybe.just xs ≡ map Maybe.just ys → xs ≡ ys
lemma-from-map-just {xs = []}      {ys = []}       p  = refl
lemma-from-map-just {xs = x ∷ xs'} {ys = y ∷ ys'}  p with ∷-injective p
lemma-from-map-just {xs = x ∷ xs'} {ys = .x ∷ ys'} p | refl , p' = cong (_∷_ x) (lemma-from-map-just p')

lemma-union-not-used : {m n : ℕ} {A : Set} (h : FinMapMaybe n A) → (h' : FinMap n A) → (is : Vec (Fin n) m) → (toList is) in-domain-of h → map just (map (flip lookup (union h h')) is) ≡ map (flip lookupM h) is
lemma-union-not-used h h' []        p = refl
lemma-union-not-used h h' (i ∷ is') p with Data.List.All.head p
lemma-union-not-used h h' (i ∷ is') p | x , lookupM-i-h≡just-x = begin
  just (lookup i (union h h')) ∷ map just (map (flip lookup (union h h')) is')
    ≡⟨ cong (flip _∷_ (map just (map (flip lookup (union h h')) is'))) (begin
      just (lookup i (union h h'))
        ≡⟨ cong just (lookup∘tabulate (λ j → maybe′ id (lookup j h') (lookupM j h)) i) ⟩
      just (maybe′ id (lookup i h') (lookupM i h))
        ≡⟨ cong just (cong (maybe′ id (lookup i h')) lookupM-i-h≡just-x) ⟩
      just (maybe′ id (lookup i h') (just x))
        ≡⟨ refl ⟩
      just x
        ≡⟨ sym lookupM-i-h≡just-x ⟩
      lookupM i h ∎) ⟩
  lookupM i h ∷ map just (map (flip lookup (union h h')) is')
    ≡⟨ cong (_∷_ (lookupM i h)) (lemma-union-not-used h h' is' (Data.List.All.tail p)) ⟩
  lookupM i h ∷ map (flip lookupM h) is' ∎

theorem-2 : {getlen : ℕ → ℕ} (get : get-type getlen) → {m : ℕ} → (v : Vec Carrier (getlen m)) → (s u : Vec Carrier m) → bff get deq s v ≡ just u → get u ≡ v
theorem-2 get v s u p with lemma-fmap-just (assoc deq (get (enumerate s)) v) (proj₂ (lemma-fmap-just (fmap (flip union (fromFunc (denumerate s))) (assoc deq (get (enumerate s)) v)) p))
theorem-2 get v s u p | h , ph = begin
  get u
    ≡⟨ lemma-from-just (begin
      just (get u)
        ≡⟨ refl ⟩
      fmap get (just u)
        ≡⟨ cong (fmap get) (sym p) ⟩
      fmap get (bff get deq s v)
        ≡⟨ cong (fmap get ∘ fmap (flip map (enumerate s) ∘ flip lookup) ∘ fmap (flip union (fromFunc (denumerate s)))) ph ⟩
      fmap get (fmap (flip map (enumerate s) ∘ flip lookup) (fmap (flip union (fromFunc (denumerate s))) (just h)))
       ≡⟨ refl ⟩
     just (get (map (flip lookup (union h (fromFunc (denumerate s)))) (enumerate s)))
       ∎) ⟩
  get (map (flip lookup (union h (fromFunc (denumerate s)))) (enumerate s))
    ≡⟨ free-theorem get (flip lookup (union h (fromFunc (denumerate s)))) (enumerate s) ⟩
  map (flip lookup (union h (fromFunc (denumerate s)))) (get (enumerate s))
     ≡⟨ lemma-from-map-just (begin
       map just (map (flip lookup (union h (fromFunc (denumerate s)))) (get (enumerate s)))
         ≡⟨ lemma-union-not-used h (fromFunc (denumerate s)) (get (enumerate s)) (lemma-assoc-domain (get (enumerate s)) v h ph) ⟩
       map (flip lookupM h) (get (enumerate s))
         ≡⟨ lemma-2 (get (enumerate s)) v h ph ⟩
       map just v
         ∎) ⟩
  v ∎
