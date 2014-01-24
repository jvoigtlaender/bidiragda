open import Relation.Binary.Core using (Decidable ; _≡_)

module Bidir (Carrier : Set) (deq : Decidable {A = Carrier} _≡_) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Level
import Category.Monad
import Category.Functor
open import Data.Maybe using (Maybe ; nothing ; just ; maybe′)
open Category.Monad.RawMonad {Level.zero} Data.Maybe.monad using (_>>=_)
open Category.Functor.RawFunctor {Level.zero} Data.Maybe.functor using (_<$>_)
open import Data.List using (List)
open import Data.List.All using (All)
open import Data.Vec using (Vec ; [] ; _∷_ ; toList ; map ; tabulate) renaming (lookup to lookupVec)
open import Data.Vec.Properties using (tabulate-∘ ; lookup∘tabulate ; map-cong ; map-∘)
open import Data.Product using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Function using (id ; _∘_ ; flip)
open import Relation.Binary.Core using (refl)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; [_] ; trans ; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

import FreeTheorems
open FreeTheorems.VecVec using (get-type ; free-theorem)
open import Generic using (just-injective ; map-just-injective ; mapMV ; mapMV-cong ; mapMV-purity ; sequenceV ; sequence-map)
open import FinMap
import CheckInsert
open CheckInsert Carrier deq
import BFF
open BFF.VecBFF Carrier deq using (assoc ; enumerate ; denumerate ; bff)

lemma-1 : {m n : ℕ} → (f : Fin n → Carrier) → (is : Vec (Fin n) m) → assoc is (map f is) ≡ just (restrict f (toList is))
lemma-1 f []        = refl
lemma-1 f (i ∷ is′) = begin
  (assoc is′ (map f is′) >>= checkInsert i (f i))
    ≡⟨ cong (λ m → m >>= checkInsert i (f i)) (lemma-1 f is′) ⟩
  checkInsert i (f i) (restrict f (toList is′))
    ≡⟨ lemma-checkInsert-restrict f i (toList is′) ⟩
  just (restrict f (toList (i ∷ is′))) ∎

lemma-lookupM-assoc : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (x : Carrier) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc (i ∷ is) (x ∷ xs) ≡ just h → lookupM i h ≡ just x
lemma-lookupM-assoc i is x xs h    p with assoc is xs
lemma-lookupM-assoc i is x xs h    () | nothing
lemma-lookupM-assoc i is x xs h    p | just h' with checkInsert i x h' | insertionresult i x h'
lemma-lookupM-assoc i is x xs .h refl | just h | ._ | same pl = pl
lemma-lookupM-assoc i is x xs ._ refl | just h' | ._ | new _ = lemma-lookupM-insert i x h'
lemma-lookupM-assoc i is x xs h () | just h' | ._ | wrong _ _ _

_in-domain-of_ : {n : ℕ} {A : Set} → (is : List (Fin n)) → (FinMapMaybe n A) → Set
_in-domain-of_ is h = All (λ i → ∃ λ x → lookupM i h ≡ just x) is

lemma-assoc-domain : {m n : ℕ} → (is : Vec (Fin n) m) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc is xs ≡ just h → (toList is) in-domain-of h
lemma-assoc-domain []         []         h ph = Data.List.All.[]
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h ph with assoc is' xs' | inspect (assoc is') xs'
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h () | nothing | [ ph' ]
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h ph | just h' | [ ph' ] with checkInsert i' x' h' | inspect (checkInsert i' x') h' | insertionresult i' x' h'
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') .h refl | just h | [ ph' ] | ._ | _ | same pl = All._∷_ (x' , pl) (lemma-assoc-domain is' xs' h ph')
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') ._ refl | just h' | [ ph' ] | ._ | [ cI≡ ] | new _ = All._∷_
  (x' , lemma-lookupM-insert i' x' h')
  (Data.List.All.map
    (λ {i} p → proj₁ p , lemma-lookupM-checkInsert i i' (proj₁ p) x' h' (insert i' x' h') (proj₂ p) cI≡)
    (lemma-assoc-domain is' xs' h' ph'))
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h () | just h' | [ ph' ] | ._ | _ | wrong _ _ _

lemma-map-lookupM-assoc : {m : ℕ} → (i : Fin m) → (x : Carrier) → (h : FinMapMaybe m Carrier) → (h' : FinMapMaybe m Carrier) → checkInsert i x h' ≡ just h → {n : ℕ} → (js : Vec (Fin m) n) → (toList js) in-domain-of h' → map (flip lookupM h) js ≡ map (flip lookupM h') js
lemma-map-lookupM-assoc i x h h' ph [] pj = refl
lemma-map-lookupM-assoc i x h h' ph (j ∷ js) (Data.List.All._∷_ (x' , pl) pj) = cong₂ _∷_
  (trans (lemma-lookupM-checkInsert j i x' x h' h pl ph) (sym pl))
  (lemma-map-lookupM-assoc i x h h' ph js pj)

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
    ≡⟨  cong (_∷_ (just x)) (lemma-map-lookupM-assoc i x h h' p is (lemma-assoc-domain is xs h' ir)) ⟩
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
  (h′↦r ∘ just) (union (restrict (denumerate s) (toList (get (enumerate s)))) (delete-many (get (enumerate s)) (fromFunc (denumerate s))))
    ≡⟨ cong (h′↦r ∘ just) (lemma-disjoint-union (denumerate s) (get (enumerate s))) ⟩
  (h′↦r ∘ just) (fromFunc (denumerate s))
    ≡⟨ refl ⟩
  mapMV (flip lookupVec (fromFunc (denumerate s))) (enumerate s)
    ≡⟨ cong (flip mapMV (enumerate s) ∘ flip lookupVec) (lemma-fromFunc-tabulate (denumerate s)) ⟩
  mapMV (flip lookupVec (tabulate (Maybe.just ∘ denumerate s))) (enumerate s)
    ≡⟨ mapMV-cong (lookup∘tabulate (Maybe.just ∘ denumerate s)) (enumerate s) ⟩
  mapMV (Maybe.just ∘ denumerate s) (enumerate s)
    ≡⟨ mapMV-purity (denumerate s) (enumerate s) ⟩
  just (map (denumerate s) (enumerate s))
    ≡⟨ cong just (lemma-map-denumerate-enumerate s) ⟩
  just s ∎
    where h↦h′ = _<$>_ (flip union (delete-many (get (enumerate s)) (fromFunc (denumerate s))))
          h′↦r = flip _>>=_ (flip mapMV (enumerate s) ∘ flip lookupVec)


lemma-<$>-just : {A B : Set} {f : A → B} {b : B} (ma : Maybe A) → f <$> ma ≡ just b → ∃ λ a → ma ≡ just a
lemma-<$>-just (just x) f<$>ma≡just-b = x , refl
lemma-<$>-just nothing  ()

lemma-union-not-used : {m n : ℕ} {A : Set} (h : FinMapMaybe n A) → (h' : FinMapMaybe n A) → (is : Vec (Fin n) m) → (toList is) in-domain-of h → map (flip lookupM (union h h')) is ≡ map (flip lookupM h) is
lemma-union-not-used h h' []        p = refl
lemma-union-not-used h h' (i ∷ is') (Data.List.All._∷_ (x , px) p') = cong₂ _∷_ (begin
      lookupM i (union h h')
        ≡⟨ lookup∘tabulate (λ j → maybe′ just (lookupM j h') (lookupM j h)) i ⟩
      maybe′ just (lookupM i h') (lookupM i h)
        ≡⟨ cong (maybe′ just (lookupM i h')) px ⟩
      maybe′ just (lookupM i h') (just x)
        ≡⟨ sym px ⟩
      lookupM i h ∎)
  (lemma-union-not-used h h' is' p')

lemma->>=-just : {A B : Set} (ma : Maybe A) {f : A → Maybe B} {b : B} → (ma >>= f) ≡ just b → ∃ λ a → ma ≡ just a
lemma->>=-just (just a) p = a , refl
lemma->>=-just nothing  ()

lemma-mapMV-just : {A B : Set} {n : ℕ} {f : A → Maybe B} {s : Vec A n} {v : Vec B n} → mapMV f s ≡ just v → All (λ x → ∃ λ y → f x ≡ just y) (toList s)
lemma-mapMV-just         {s = []}     p = Data.List.All.[]
lemma-mapMV-just {f = f} {s = x ∷ xs} p with f x | inspect f x
lemma-mapMV-just         {s = x ∷ xs} () | nothing | _
lemma-mapMV-just {f = f} {s = x ∷ xs} p  | just y  | [ py ] with mapMV f xs | inspect (mapMV f) xs
lemma-mapMV-just         {s = x ∷ xs} () | just y  | [ py ] | nothing | _
lemma-mapMV-just         {s = x ∷ xs} p  | just y  | [ py ] | just ys | [ pys ] = (y , py) Data.List.All.∷ (lemma-mapMV-just pys)

lemma-just-sequence : {A : Set} {n : ℕ} → (v : Vec A n) → sequenceV (map just v) ≡ just v
lemma-just-sequence [] = refl
lemma-just-sequence (x ∷ xs) rewrite lemma-just-sequence xs = refl

lemma-mapM-successful : {A B : Set} {f : A → Maybe B} {n : ℕ} → (v : Vec A n) → {r : Vec B n} → mapMV f v ≡ just r → ∃ λ w → map f v ≡ map just w
lemma-mapM-successful         []      p = [] , refl
lemma-mapM-successful {f = f} (x ∷ xs) p with f x | mapMV f xs | inspect (mapMV f) xs
lemma-mapM-successful         (x ∷ xs) () | nothing | _ | _
lemma-mapM-successful         (x ∷ xs) () | just y | nothing | _
lemma-mapM-successful         (x ∷ xs) p  | just y | just ys | [ p′ ] with lemma-mapM-successful xs p′
lemma-mapM-successful         (x ∷ xs) p  | just y | just ys | [ p′ ] | w , pw = y ∷ w , cong (_∷_ (just y)) pw


lemma-get-mapMV : {A B : Set} {f : A → Maybe B} {n : ℕ} {v : Vec A n} {r : Vec B n} → mapMV f v ≡ just r → {getlen : ℕ → ℕ} (get : get-type getlen) → get <$> mapMV f v ≡ mapMV f (get v)
lemma-get-mapMV {f = f} {v = v} p get = let w , pw = lemma-mapM-successful v p in begin
  get <$> mapMV f v
    ≡⟨ cong (_<$>_ get) (sym (sequence-map f v)) ⟩
  get <$> (sequenceV (map f v))
    ≡⟨ cong (_<$>_ get ∘ sequenceV) pw ⟩
  get <$> (sequenceV (map just w))
    ≡⟨ cong (_<$>_ get) (lemma-just-sequence w) ⟩
  get <$> just w
    ≡⟨ sym (lemma-just-sequence (get w)) ⟩
  sequenceV (map just (get w))
    ≡⟨ cong sequenceV (sym (free-theorem get just w)) ⟩
  sequenceV (get (map just w))
    ≡⟨ cong (sequenceV ∘ get) (sym pw) ⟩
  sequenceV (get (map f v))
    ≡⟨ cong sequenceV (free-theorem get f v) ⟩
  sequenceV (map f (get v))
    ≡⟨ sequence-map f (get v) ⟩
  mapMV f (get v) ∎

theorem-2 : {getlen : ℕ → ℕ} (get : get-type getlen) → {m : ℕ} → (v : Vec Carrier (getlen m)) → (s u : Vec Carrier m) → bff get s v ≡ just u → get u ≡ v
theorem-2 get v s u p with (lemma->>=-just ((flip union (delete-many (get (enumerate s)) (fromFunc (denumerate s)))) <$> (assoc (get (enumerate s)) v)) p)
theorem-2 get v s u p | h′ , ph′ with (lemma-<$>-just (assoc (get (enumerate s)) v) ph′)
theorem-2 get v s u p | h′ , ph′ | h , ph = just-injective (begin
  get <$> (just u)
    ≡⟨ cong (_<$>_ get) (sym p) ⟩
  get <$> (bff get s v)
    ≡⟨ cong (_<$>_ get ∘ flip _>>=_ h′↦r ∘ _<$>_ h↦h′) ph ⟩
  get <$> mapMV (flip lookupM (h↦h′ h)) s′
    ≡⟨ lemma-get-mapMV (trans (cong (flip _>>=_ h′↦r ∘ _<$>_ h↦h′) (sym ph)) p) get ⟩
  mapMV (flip lookupM (h↦h′ h)) (get s′)
    ≡⟨ sym (sequence-map (flip lookupM (h↦h′ h)) (get s′)) ⟩
  sequenceV (map (flip lookupM (h↦h′ h)) (get s′))
    ≡⟨ cong sequenceV (lemma-union-not-used h g′ (get s′) (lemma-assoc-domain (get s′) v h ph)) ⟩
  sequenceV (map (flip lookupM h) (get s′))
    ≡⟨ cong sequenceV (lemma-2 (get s′) v h ph) ⟩
  sequenceV (map just v)
    ≡⟨ lemma-just-sequence v ⟩
  just v ∎)
    where s′   = enumerate s
          g    = fromFunc (denumerate s)
          g′   = delete-many (get s′) g
          h↦h′ = flip union g′
          h′↦r = flip mapMV s′ ∘ flip lookupM
