open import Relation.Binary.Core using (Decidable ; _≡_)

module Precond (Carrier : Set) (deq : Decidable {A = Carrier} _≡_) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List ; [] ; _∷_)
open import Level using () renaming (zero to ℓ₀)
import Category.Monad
import Category.Functor
open import Data.Maybe using (Maybe ; nothing ; just ; maybe′)
open Category.Monad.RawMonad {Level.zero} Data.Maybe.monad using (_>>=_)
open Category.Functor.RawFunctor {Level.zero} Data.Maybe.functor using (_<$>_)
open import Data.Vec using (Vec ; [] ; _∷_ ; map ; lookup ; toList)
open import Data.Vec.Properties using (map-cong ; map-∘ ; tabulate-∘)
import Data.List.All
open import Data.List.Any using (here ; there)
open Data.List.Any.Membership-≡ using (_∉_)
open import Data.Maybe using (just)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Function using (flip ; _∘_ ; id)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (refl ; cong ; inspect ; [_] ; sym ; decSetoid)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)
open import Relation.Nullary using (yes ; no)

open import Structures using (IsFunctor ; module Shaped ; Shaped)
open import FinMap using (FinMapMaybe ; lookupM ; union ; fromFunc ; empty ; insert ; lemma-lookupM-empty ; delete-many ; lemma-tabulate-∘ ; delete ; lemma-lookupM-delete ; lemma-lookupM-fromFunc ; reshape ; lemma-reshape-id)
import CheckInsert
open CheckInsert (decSetoid deq) using (checkInsert ; lemma-checkInsert-new ; lemma-lookupM-checkInsert-other)
import BFF
import Bidir
open Bidir (decSetoid deq) using (_in-domain-of_ ; lemma-assoc-domain)
import GetTypes
open GetTypes.PartialShapeShape using (Get ; module Get)
open BFF.PartialShapeBFF (decSetoid deq) using (assoc ; enumerate ; denumerate ; bff)

lemma-maybe-just : {A : Set} → (a : A) → (ma : Maybe A) → maybe′ Maybe.just (just a) ma ≡ Maybe.just (maybe′ id a ma)
lemma-maybe-just a (just x) = refl
lemma-maybe-just a nothing = refl

lemma-union-delete-fromFunc : {m n : ℕ} {A : Set} {is : Vec (Fin n) m} {h : FinMapMaybe n A} {g : Fin n → A} → is in-domain-of h → ∃ λ v → union h (delete-many is (fromFunc g)) ≡ fromFunc v
lemma-union-delete-fromFunc {is = []} {h = h} {g = g} p = _ , (lemma-tabulate-∘ (λ f → begin
      maybe′ just (lookupM f (fromFunc g)) (lookupM f h)
        ≡⟨ cong (flip (maybe′ just) (lookupM f h)) (lemma-lookupM-fromFunc g f) ⟩
      maybe′ just (just (g f)) (lookupM f h)
        ≡⟨ lemma-maybe-just (g f) (lookupM f h) ⟩
      just (maybe′ id (g f) (lookupM f h)) ∎))
lemma-union-delete-fromFunc {n = n} {is = i ∷ is} {h = h} {g = g} (Data.List.All._∷_ (x , px) ps) = _ , (begin
  union h (delete i (delete-many is (fromFunc g)))
    ≡⟨ lemma-tabulate-∘ inner ⟩
  union h (delete-many is (fromFunc g))
    ≡⟨ proj₂ (lemma-union-delete-fromFunc ps) ⟩
  _ ∎)
  where inner : (f : Fin n) → maybe′ just (lookupM f (delete i (delete-many is (fromFunc g)))) (lookup f h) ≡ maybe′ just (lookupM f (delete-many is (fromFunc g))) (lookup f h)
        inner f with f ≟ i
        inner .i | yes refl = begin
          maybe′ just (lookupM i (delete i (delete-many is (fromFunc g)))) (lookup i h)
            ≡⟨ cong (maybe′ just _) px ⟩
          just x
            ≡⟨ cong (maybe′ just _) (sym px) ⟩
          maybe′ just (lookupM i (delete-many is (fromFunc g))) (lookup i h) ∎
        inner f | no f≢i = cong (flip (maybe′ just) (lookup f h)) (lemma-lookupM-delete (delete-many is (fromFunc g)) f≢i)

module _ (G : Get) where
  open Get G
  open Shaped ViewShapeT using () renaming (content to contentV)

  assoc-enough : {i : I} → (j : I) → (s : SourceContainer Carrier (gl₁ i)) → (v : ViewContainer Carrier (gl₂ j)) → ∃ (λ h → assoc (contentV (get (enumerate SourceShapeT (gl₁ j)))) (contentV v) ≡ just h) → ∃ λ u → bff G j s v ≡ just u
  assoc-enough {i} j s v (h , p) = _ , cong (_<$>_ ((λ f → fmapS f t) ∘ flip lookupM) ∘ _<$>_ (flip union (reshape g′ (Shaped.arity SourceShapeT (gl₁ j))))) p
    where g′ = delete-many (contentV (get (enumerate SourceShapeT (gl₁ i)))) (fromFunc (denumerate SourceShapeT s))
          t  = enumerate SourceShapeT (gl₁ j)

module _ (G : Get) where
  open Get G
  open Shaped ViewShapeT using () renaming (content to contentV)

  assoc-enough′ : {i : I} → (s : SourceContainer Carrier (gl₁ i)) → (v : ViewContainer Carrier (gl₂ i)) → ∃ (λ h → assoc (contentV (get (enumerate SourceShapeT (gl₁ i)))) (contentV v) ≡ just h) → ∃ λ u → bff G i s v ≡ just (fmapS just u)
  assoc-enough′ {i} s v (h , p) = _ , (begin
    bff G i s v
      ≡⟨ proj₂ (assoc-enough G i s v (h , p)) ⟩
    just (fmapS (flip lookupM (union h (reshape g′ (Shaped.arity SourceShapeT (gl₁ i))))) t)
      ≡⟨ cong just (begin _
          ≡⟨ cong ((λ f → fmapS f t) ∘ flip lookupM ∘ union h) (lemma-reshape-id g′) ⟩
        fmapS (flip lookupM (union h g′)) t
          ≡⟨ cong ((λ f → fmapS f t) ∘ flip lookupM) (proj₂ wp) ⟩
        fmapS (flip lookupM (fromFunc (proj₁ wp))) t
          ≡⟨ IsFunctor.cong (Shaped.isFunctor SourceShapeT (gl₁ i)) (lemma-lookupM-fromFunc (proj₁ wp)) t ⟩
        fmapS (Maybe.just ∘ proj₁ wp) t
          ≡⟨ IsFunctor.composition (Shaped.isFunctor SourceShapeT (gl₁ i)) just (proj₁ wp) t ⟩
        fmapS Maybe.just (fmapS (proj₁ wp) t) ∎) ⟩ _ ∎)
    where s′ = enumerate SourceShapeT (gl₁ i)
          g  = fromFunc (denumerate SourceShapeT s)
          g′ = delete-many (contentV (get s′)) g
          t  = enumerate SourceShapeT (gl₁ i)
          wp = lemma-union-delete-fromFunc (lemma-assoc-domain (contentV (get t)) (contentV v) p)

data All-different {A : Set} : List A → Set where
  different-[] : All-different []
  different-∷  : {x : A} {xs : List A} → x ∉ xs → All-different xs → All-different (x ∷ xs)

lemma-∉-lookupM-assoc : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (xs : Vec Carrier m) → {h : FinMapMaybe n Carrier} → assoc is xs ≡ just h → (i ∉ toList is) → lookupM i h ≡ nothing
lemma-∉-lookupM-assoc i []         []         refl i∉is = lemma-lookupM-empty i
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') ph i∉is with assoc is' xs' | inspect (assoc is') xs'
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') () i∉is | nothing | [ ph' ]
lemma-∉-lookupM-assoc i (i' ∷ is') (x' ∷ xs') {h} ph i∉is | just h' | [ ph' ] = begin
  lookupM i h
    ≡⟨ lemma-lookupM-checkInsert-other i i' (i∉is ∘ here) x' h' ph ⟩
  lookupM i h'
    ≡⟨ lemma-∉-lookupM-assoc i is' xs' ph' (i∉is ∘ there) ⟩
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
    ≡⟨ lemma-checkInsert-new u v h (lemma-∉-lookupM-assoc u us vs p' u∉us) ⟩
  just (insert u v h) ∎)
