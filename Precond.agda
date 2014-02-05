open import Relation.Binary.Core using (Decidable ; _≡_)

module Precond (Carrier : Set) (deq : Decidable {A = Carrier} _≡_) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Props using (_≟_)
open import Data.List using (List ; [] ; _∷_)
import Level
import Category.Monad
import Category.Functor
open import Data.Maybe using (Maybe ; nothing ; just ; maybe′)
open Category.Monad.RawMonad {Level.zero} Data.Maybe.monad using (_>>=_)
open Category.Functor.RawFunctor {Level.zero} Data.Maybe.functor using (_<$>_)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; toList ; tabulate)
open import Data.Vec.Properties using (map-cong ; map-∘ ; tabulate-∘)
import Data.List.All
open import Data.List.Any using (here ; there)
open Data.List.Any.Membership-≡ using (_∉_)
open import Data.Maybe using (just)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Function using (flip ; _∘_ ; id)
open import Relation.Binary.PropositionalEquality using (refl ; cong ; inspect ; [_] ; sym ; decSetoid)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)
open import Relation.Nullary using (yes ; no)

open import Generic using (mapMV ; sequenceV ; sequence-map)
open import FinMap using (FinMapMaybe ; lookupM ; union ; fromFunc ; empty ; insert ; lemma-lookupM-empty ; delete-many ; lemma-tabulate-∘ ; delete ; lemma-lookupM-delete ; lemma-lookupM-fromFunc)
import CheckInsert
open CheckInsert (decSetoid deq) using (checkInsert ; lemma-checkInsert-new ; lemma-lookupM-checkInsert-other)
import BFF
import Bidir
open Bidir (decSetoid deq) using (_in-domain-of_ ; lemma-assoc-domain ; lemma-just-sequence)
import GetTypes
open GetTypes.VecVec using (Get ; module Get)
open BFF.VecBFF (decSetoid deq) using (assoc ; enumerate ; denumerate ; bff)

lemma-maybe-just : {A : Set} → (a : A) → (ma : Maybe A) → maybe′ Maybe.just (just a) ma ≡ Maybe.just (maybe′ id a ma)
lemma-maybe-just a (just x) = refl
lemma-maybe-just a nothing = refl

lemma-union-delete-fromFunc : {m n : ℕ} {A : Set} {is : Vec (Fin n) m} {h : FinMapMaybe n A} {g : Fin n → A} → (toList is) in-domain-of h → ∃ λ v → union h (delete-many is (fromFunc g)) ≡ fromFunc v
lemma-union-delete-fromFunc {is = []} {h = h} {g = g} p = _ , (begin
  union h (fromFunc g)
    ≡⟨ lemma-tabulate-∘ (λ f → begin
      maybe′ just (lookupM f (fromFunc g)) (lookupM f h)
        ≡⟨ cong (flip (maybe′ just) (lookupM f h)) (lemma-lookupM-fromFunc g f) ⟩
      maybe′ just (just (g f)) (lookupM f h)
        ≡⟨ lemma-maybe-just (g f) (lookupM f h) ⟩
      just (maybe′ id (g f) (lookupM f h)) ∎) ⟩
  tabulate (λ f → just (maybe′ id (g f) (lookup f h)))
    ≡⟨ tabulate-∘ just (λ f → maybe′ id (g f) (lookup f h)) ⟩
  map just (tabulate (λ f → maybe′ id (g f) (lookup f h))) ∎)
lemma-union-delete-fromFunc {n = n} {is = i ∷ is} {h = h} {g = g} (Data.List.All._∷_ (x , px) ps) = _ , (begin
  union h (delete i (delete-many is (fromFunc g)))
    ≡⟨ lemma-tabulate-∘ inner ⟩
  union h (delete-many is (fromFunc g))
    ≡⟨ proj₂ (lemma-union-delete-fromFunc ps) ⟩
  map just _ ∎)
  where inner : (f : Fin n) → maybe′ just (lookupM f (delete i (delete-many is (fromFunc g)))) (lookup f h) ≡ maybe′ just (lookupM f (delete-many is (fromFunc g))) (lookup f h)
        inner f with f ≟ i
        inner .i | yes refl = begin
          maybe′ just (lookupM i (delete i (delete-many is (fromFunc g)))) (lookup i h)
            ≡⟨ cong (maybe′ just _) px ⟩
          just x
            ≡⟨ cong (maybe′ just _) (sym px) ⟩
          maybe′ just (lookupM i (delete-many is (fromFunc g))) (lookup i h) ∎
        inner f | no f≢i = cong (flip (maybe′ just) (lookup f h)) (lemma-lookupM-delete (delete-many is (fromFunc g)) f≢i)

assoc-enough : (G : Get) → {m : ℕ} → (s : Vec Carrier m) → (v : Vec Carrier (Get.getlen G m)) → ∃ (λ h → assoc (Get.get G (enumerate s)) v ≡ just h) → ∃ λ u → bff G s v ≡ just u
assoc-enough G s v (h , p) = _ , (begin
  bff G s v
    ≡⟨ cong (flip _>>=_ (flip mapMV s′ ∘ flip lookupM) ∘ _<$>_ (flip union g′)) p ⟩
  mapMV (flip lookupM (union h g′)) s′
    ≡⟨ sym (sequence-map (flip lookupM (union h g′)) s′) ⟩
  sequenceV (map (flip lookupM (union h g′)) s′)
    ≡⟨ cong (sequenceV ∘ flip map s′ ∘ flip lookupM) (proj₂ wp) ⟩
  sequenceV (map (flip lookupM (fromFunc (proj₁ wp))) s′)
    ≡⟨ cong sequenceV (map-cong (lemma-lookupM-fromFunc (proj₁ wp)) s′) ⟩
  sequenceV (map (Maybe.just ∘ proj₁ wp) s′)
    ≡⟨ cong sequenceV (map-∘ just (proj₁ wp) s′) ⟩
  sequenceV (map Maybe.just (map (proj₁ wp) s′))
    ≡⟨ lemma-just-sequence (map (proj₁ wp) s′) ⟩
  just (map (proj₁ wp) s′) ∎)
  where open Get G
        s′ = enumerate s
        g  = fromFunc (denumerate s)
        g′ = delete-many (get s′) g
        wp = lemma-union-delete-fromFunc (lemma-assoc-domain (get s′) v h p)

data All-different {A : Set} : List A → Set where
  different-[] : All-different []
  different-∷  : {x : A} {xs : List A} → x ∉ xs → All-different xs → All-different (x ∷ xs)

lemma-∉-lookupM-assoc : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc is xs ≡ just h → (i ∉ toList is) → lookupM i h ≡ nothing
lemma-∉-lookupM-assoc i []         []         .empty refl i∉is = lemma-lookupM-empty i
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') h ph i∉is with assoc is' xs' | inspect (assoc is') xs'
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') h () i∉is | nothing | [ ph' ]
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') h ph i∉is | just h' | [ ph' ] = begin
  lookupM i h
    ≡⟨ sym (lemma-lookupM-checkInsert-other i i' (i∉is ∘ here) x' h' h ph) ⟩
  lookupM i h'
    ≡⟨ lemma-∉-lookupM-assoc i is' xs' h' ph' (i∉is ∘ there) ⟩
  nothing ∎

different-assoc : {m n : ℕ} → (u : Vec (Fin n) m) → (v : Vec Carrier m) → All-different (toList u) → ∃ λ h → assoc u v ≡ just h
different-assoc []       []       p = empty , refl
different-assoc (u ∷ us) (v ∷ vs) (different-∷ u∉us diff-us) with different-assoc us vs diff-us
different-assoc (u ∷ us) (v ∷ vs) (different-∷ u∉us diff-us) | h , p' = insert u v h , (begin
  assoc (u ∷ us) (v ∷ vs)
    ≡⟨ refl ⟩
  (assoc us vs >>= checkInsert u v)
    ≡⟨ cong (flip _>>=_ (checkInsert u v)) p' ⟩
  checkInsert u v h
    ≡⟨ lemma-checkInsert-new u v h (lemma-∉-lookupM-assoc u us vs h p' u∉us) ⟩
  just (insert u v h) ∎)
