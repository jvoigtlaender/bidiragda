open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary using (DecSetoid)

module Bidir (A : DecSetoid ℓ₀ ℓ₀) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Level
import Category.Monad
import Category.Functor
open import Data.Maybe using (Maybe ; nothing ; just ; maybe′ ; drop-just) renaming (setoid to MaybeSetoid ; Eq to MaybeEq)
open Category.Monad.RawMonad {Level.zero} Data.Maybe.monad using (_>>=_)
open Category.Functor.RawFunctor {Level.zero} Data.Maybe.functor using (_<$>_)
open import Data.List using (List)
open import Data.List.All using (All)
open import Data.Vec using (Vec ; [] ; _∷_ ; toList ; map ; allFin) renaming (lookup to lookupVec)
open import Data.Vec.Equality using () renaming (module Equality to VecEq)
open import Data.Vec.Properties using (lookup∘tabulate ; map-cong ; map-∘ ; map-lookup-allFin)
open import Data.Product using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Function using (id ; _∘_ ; flip)
open import Relation.Binary.Core using (refl ; _≡_)
open import Relation.Binary.Indexed using (_at_) renaming (Setoid to ISetoid)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; [_] ; trans ; cong₂ ; decSetoid ; module ≡-Reasoning) renaming (setoid to EqSetoid)
open import Relation.Binary using (Setoid ; module Setoid ; module DecSetoid)
import Relation.Binary.EqReasoning as EqR

open import Structures using (Functor ; IsFunctor ; Shaped ; module Shaped)
open import Instances using (MaybeFunctor)
import GetTypes
open GetTypes.PartialShapeVec using (Get ; module Get)
open import Generic using (mapMV ; mapMV-cong ; mapMV-purity ; sequenceV ; VecISetoid ; just-injective)
open import FinMap
import CheckInsert
open CheckInsert A
import BFF
open BFF.PartialShapeBFF A using (assoc ; enumerate ; denumerate ; bff)
open Setoid using () renaming (_≈_ to _∋_≈_)
open module A = DecSetoid A using (Carrier) renaming (_≟_ to deq)

module SetoidReasoning where
 infix 1 begin⟨_⟩_
 infixr 2 _≈⟨_⟩_ _≡⟨_⟩_
 infix 2 _∎
 begin⟨_⟩_ : (X : Setoid ℓ₀ ℓ₀) → {x y : Setoid.Carrier X} → EqR._IsRelatedTo_ X x y → X ∋ x ≈ y
 begin⟨_⟩_ X p = EqR.begin_ X p
 _∎ : {X : Setoid ℓ₀ ℓ₀} → (x : Setoid.Carrier X) → EqR._IsRelatedTo_ X x x
 _∎ {X} = EqR._∎ X
 _≈⟨_⟩_ : {X : Setoid ℓ₀ ℓ₀} → (x : Setoid.Carrier X) → {y z : Setoid.Carrier X} → X ∋ x ≈ y → EqR._IsRelatedTo_ X y z → EqR._IsRelatedTo_ X x z
 _≈⟨_⟩_ {X} = EqR._≈⟨_⟩_ X

 _≡⟨_⟩_ : {X : Setoid ℓ₀ ℓ₀} → (x : Setoid.Carrier X) → {y z : Setoid.Carrier X} → x ≡ y → EqR._IsRelatedTo_ X y z → EqR._IsRelatedTo_ X x z
 _≡⟨_⟩_ {X} = EqR._≡⟨_⟩_ X

lemma-1 : {m n : ℕ} → (f : Fin n → Carrier) → (is : Vec (Fin n) m) → assoc is (map f is) ≡ just (restrict f (toList is))
lemma-1 f []        = refl
lemma-1 f (i ∷ is′) = begin
  (assoc is′ (map f is′) >>= checkInsert i (f i))
    ≡⟨ cong (λ m → m >>= checkInsert i (f i)) (lemma-1 f is′) ⟩
  checkInsert i (f i) (restrict f (toList is′))
    ≡⟨ lemma-checkInsert-restrict f i (toList is′) ⟩
  just (restrict f (toList (i ∷ is′))) ∎
  where open ≡-Reasoning

lemma-lookupM-checkInserted : {n : ℕ} → (i : Fin n) → (x : Carrier) → (h h' : FinMapMaybe n Carrier) → checkInsert i x h ≡ just h' → MaybeSetoid A.setoid ∋ lookupM i h' ≈ just x
lemma-lookupM-checkInserted i x h h' p with checkInsert i x h | insertionresult i x h
lemma-lookupM-checkInserted i x h .h refl | ._ | same x' x≈x' pl = begin
  lookupM i h
    ≡⟨ pl ⟩
  just x'
    ≈⟨ MaybeEq.just (Setoid.sym A.setoid x≈x') ⟩
  just x ∎
  where open EqR (MaybeSetoid A.setoid)
lemma-lookupM-checkInserted i x h ._ refl | ._ | new _ = Setoid.reflexive (MaybeSetoid A.setoid) (lemma-lookupM-insert i x h)
lemma-lookupM-checkInserted i x h h' () | ._ | wrong _ _ _

_in-domain-of_ : {n : ℕ} {A : Set} → (is : List (Fin n)) → (FinMapMaybe n A) → Set
_in-domain-of_ is h = All (λ i → ∃ λ x → lookupM i h ≡ just x) is

lemma-assoc-domain : {m n : ℕ} → (is : Vec (Fin n) m) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc is xs ≡ just h → (toList is) in-domain-of h
lemma-assoc-domain []         []         h ph = Data.List.All.[]
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h ph with assoc is' xs' | inspect (assoc is') xs'
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h () | nothing | [ ph' ]
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') h ph | just h' | [ ph' ] with checkInsert i' x' h' | inspect (checkInsert i' x') h' | insertionresult i' x' h'
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') .h refl | just h | [ ph' ] | ._ | _ | same x _ pl = All._∷_ (x , pl) (lemma-assoc-domain is' xs' h ph')
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

lemma-2 : {m n : ℕ} → (is : Vec (Fin n) m) → (v : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc is v ≡ just h → VecISetoid (MaybeSetoid A.setoid) at _ ∋ map (flip lookupM h) is ≈ map just v
lemma-2 []       []       h p = ISetoid.refl (VecISetoid (MaybeSetoid A.setoid))
lemma-2 (i ∷ is) (x ∷ xs) h p with assoc is xs | inspect (assoc is) xs
lemma-2 (i ∷ is) (x ∷ xs) h () | nothing | _
lemma-2 (i ∷ is) (x ∷ xs) h p | just h' | [ ir ] = begin
  lookupM i h ∷ map (flip lookupM h) is
    ≈⟨ VecEq._∷-cong_ (lemma-lookupM-checkInserted i x h' h p) (ISetoid.refl (VecISetoid (MaybeSetoid A.setoid))) ⟩
  just x ∷ map (flip lookupM h) is
    ≡⟨  cong (_∷_ (just x)) (lemma-map-lookupM-assoc i x h h' p is (lemma-assoc-domain is xs h' ir)) ⟩
  just x ∷ map (flip lookupM h') is
    ≈⟨ VecEq._∷-cong_ (Setoid.refl (MaybeSetoid A.setoid)) (lemma-2 is xs h' ir) ⟩
  just x ∷ map just xs ∎
  where open EqR (VecISetoid (MaybeSetoid A.setoid) at _)

lemma-fmap-denumerate-enumerate : {S : Set} {C : Set → S → Set} → (ShapeT : Shaped S C) → {α : Set} {s : S} → (c : C α s) → Shaped.fmap ShapeT (denumerate ShapeT c) (enumerate ShapeT s) ≡ c
lemma-fmap-denumerate-enumerate {S} {C} ShapeT {s = s} c = begin
  fmap (denumerate ShapeT c) (fill s (allFin (arity s)))
    ≡⟨ fill-fmap (denumerate ShapeT c) s (allFin (arity s)) ⟩
  fill s (map (flip lookupVec (content c)) (allFin (arity s)))
    ≡⟨ cong (fill s) (map-lookup-allFin (content c)) ⟩
  fill s (content c)
    ≡⟨ content-fill c ⟩
  c ∎
  where open ≡-Reasoning
        open Shaped ShapeT


theorem-1 : (G : Get) → {i : Get.|I| G} → (s : Get.Container G Carrier (Get.|gl₁| G i)) → bff G i s (Get.get G s) ≡ just (Get.fmap G just s)
theorem-1 G {i} s = begin
  bff G i s (get s)
    ≡⟨ cong (bff G i s ∘ get) (sym (lemma-fmap-denumerate-enumerate ShapeT s)) ⟩
  bff G i s (get (fmap f t))
    ≡⟨ cong (bff G i s) (free-theorem f t) ⟩
  bff G i s (map f (get t))
    ≡⟨ refl ⟩
  h′↦r <$> (h↦h′ <$> (assoc (get t) (map f (get t))))
    ≡⟨ cong (_<$>_ h′↦r ∘ _<$>_ h↦h′) (lemma-1 f (get t)) ⟩
  (Maybe.just ∘ h′↦r ∘ h↦h′) (restrict f (toList (get t)))
    ≡⟨ cong just (begin
      h′↦r (union (restrict f (toList (get t))) (reshape g′ (arity (|gl₁| i))))
        ≡⟨ cong (h′↦r ∘ union (restrict f (toList (get t)))) (lemma-reshape-id g′) ⟩
      h′↦r (union (restrict f (toList (get t))) g′)
        ≡⟨ cong h′↦r (lemma-disjoint-union f (get t)) ⟩
      h′↦r (fromFunc f)
        ≡⟨ refl ⟩
      fmap (flip lookupM (fromFunc f)) t
        ≡⟨ IsFunctor.cong (isFunctor (|gl₁| i)) (lemma-lookupM-fromFunc f) t ⟩
      fmap (Maybe.just ∘ f) t
        ≡⟨ IsFunctor.composition (isFunctor (|gl₁| i)) just f t ⟩
      fmap just (fmap f t)
        ≡⟨ cong (fmap just) (lemma-fmap-denumerate-enumerate ShapeT s) ⟩
      fmap just s ∎) ⟩ _ ∎
    where open ≡-Reasoning
          open Get G
          t    = enumerate ShapeT (|gl₁| i)
          f    = denumerate ShapeT s
          g′   = delete-many (get t) (fromFunc f)
          h↦h′ = flip union (reshape g′ (arity (|gl₁| i)))
          h′↦r = (λ f′ → fmap f′ t) ∘ flip lookupM


lemma-<$>-just : {A B : Set} {f : A → B} {b : B} (ma : Maybe A) → f <$> ma ≡ just b → ∃ λ a → ma ≡ just a
lemma-<$>-just (just x) f<$>ma≡just-b = x , refl
lemma-<$>-just nothing  ()

lemma-union-not-used : {m n n' : ℕ} {A : Set} (h : FinMapMaybe n A) → (h' : FinMapMaybe n' A) → (is : Vec (Fin n) m) → (toList is) in-domain-of h → map (flip lookupM (union h (reshape h' n))) is ≡ map (flip lookupM h) is
lemma-union-not-used         h h' []        p = refl
lemma-union-not-used {n = n} h h' (i ∷ is') (Data.List.All._∷_ (x , px) p') = cong₂ _∷_ (begin
      lookupM i (union h (reshape h' n))
        ≡⟨ lookup∘tabulate (λ j → maybe′ just (lookupM j (reshape h' n)) (lookupM j h)) i ⟩
      maybe′ just (lookupM i (reshape h' n)) (lookupM i h)
        ≡⟨ cong (maybe′ just (lookupM i (reshape h' n))) px ⟩
      maybe′ just (lookupM i (reshape h' n)) (just x)
        ≡⟨ sym px ⟩
      lookupM i h ∎)
  (lemma-union-not-used h h' is' p')
  where open ≡-Reasoning

lemma->>=-just : {A B : Set} (ma : Maybe A) {f : A → Maybe B} {b : B} → (ma >>= f) ≡ just b → ∃ λ a → ma ≡ just a
lemma->>=-just (just a) p = a , refl
lemma->>=-just nothing  ()

lemma-just-sequenceV : {A : Set} {n : ℕ} → (v : Vec A n) → sequenceV (map just v) ≡ just v
lemma-just-sequenceV []       = refl
lemma-just-sequenceV (x ∷ xs) = cong (_<$>_ (_∷_ x)) (lemma-just-sequenceV xs)

lemma-just-sequence : (G : Get) → {A : Set} {i : Get.|I| G} → (c : Get.Container G A (Get.|gl₁| G i)) → Get.sequence G (Get.fmap G just c) ≡ just c
lemma-just-sequence G {i = i} c = begin
  fill (|gl₁| i) <$> sequenceV (content (fmap just c))
    ≡⟨ cong (_<$>_ (fill (|gl₁| i)) ∘ sequenceV) (fmap-content just c) ⟩
  fill (|gl₁| i) <$> sequenceV (map just (content c))
    ≡⟨ cong (_<$>_ (fill (|gl₁| i))) (lemma-just-sequenceV (content c)) ⟩
  fill (|gl₁| i) <$> just (content c)
    ≡⟨ cong just (content-fill c) ⟩
  just c ∎
  where open ≡-Reasoning
        open Get G

lemma-sequenceV-successful : {A : Set} {n : ℕ} → (v : Vec (Maybe A) n) → {r : Vec A n} → sequenceV v ≡ just r → v ≡ map just r
lemma-sequenceV-successful []             {r = []}       p = refl
lemma-sequenceV-successful (just x ∷ xs)                 p with sequenceV xs | inspect sequenceV xs
lemma-sequenceV-successful (just x ∷ xs)                 () | nothing | _
lemma-sequenceV-successful (just x ∷ xs)  {r = .x ∷ .ys} refl  | just ys | [ p′ ] = cong (_∷_ (just x)) (lemma-sequenceV-successful xs p′)
lemma-sequenceV-successful (nothing ∷ xs)                ()

lemma-sequence-successful : (G : Get) → {A : Set} {i : Get.|I| G} → (c : Get.Container G (Maybe A) (Get.|gl₁| G i)) → {r : Get.Container G A (Get.|gl₁| G i)} → Get.sequence G c ≡ just r → c ≡ Get.fmap G just r
lemma-sequence-successful G {i = i} c {r} p = just-injective (sym (begin
  fill (|gl₁| i) <$> (map just <$> (content <$> just r))
    ≡⟨ cong (_<$>_ (fill (|gl₁| i)) ∘ _<$>_ (map just)) (begin
      content <$> just r
        ≡⟨ cong (_<$>_ content) (sym p) ⟩
      content <$> (fill (|gl₁| i) <$> sequenceV (content c))
        ≡⟨ sym (Functor.composition MaybeFunctor content (fill (|gl₁| i)) (sequenceV (content c))) ⟩
      content ∘ fill (|gl₁| i) <$> sequenceV (content c)
        ≡⟨ Functor.cong MaybeFunctor (fill-content (|gl₁| i)) (sequenceV (content c)) ⟩
      id <$> sequenceV (content c)
        ≡⟨ Functor.identity MaybeFunctor (sequenceV (content c)) ⟩
      sequenceV (content c)
        ≡⟨ cong sequenceV (lemma-sequenceV-successful (content c) (proj₂ wp)) ⟩
      sequenceV (map just (proj₁ wp))
        ≡⟨ lemma-just-sequenceV (proj₁ wp) ⟩
      just (proj₁ (lemma-<$>-just (sequenceV (content c)) p)) ∎) ⟩
  fill (|gl₁| i) <$> (map just <$> just (proj₁ (lemma-<$>-just (sequenceV (content c)) p)))
    ≡⟨ cong (_<$>_ (fill (|gl₁| i)) ∘ just) (sym (lemma-sequenceV-successful (content c) (proj₂ wp))) ⟩
  fill (|gl₁| i) <$> just (content c)
    ≡⟨ cong just (content-fill c) ⟩
  just c ∎))
  where open ≡-Reasoning
        open Get G
        wp = lemma-<$>-just (sequenceV (content c)) p

lemma-get-sequence : {A : Set} → (G : Get) → {i : Get.|I| G} {v : Get.Container G (Maybe A) (Get.|gl₁| G i)} {r : Get.Container G A (Get.|gl₁| G i)} → Get.sequence G v ≡ just r → Get.get G <$> Get.sequence G v ≡ sequenceV (Get.get G v)
lemma-get-sequence G {v = v} {r = r} p = begin
  get <$> sequence v
    ≡⟨ cong (_<$>_ get ∘ sequence) (lemma-sequence-successful G v p) ⟩
  get <$> sequence (fmap just r)
    ≡⟨ cong (_<$>_ get) (lemma-just-sequence G r) ⟩
  get <$> just r
    ≡⟨ sym (lemma-just-sequenceV (get r)) ⟩
  sequenceV (map just (get r))
    ≡⟨ cong sequenceV (sym (free-theorem just r)) ⟩
  sequenceV (get (fmap just r))
    ≡⟨ cong (sequenceV ∘ get) (sym (lemma-sequence-successful G v p)) ⟩
  sequenceV (get v) ∎
  where open ≡-Reasoning
        open Get G

sequence-cong : {S : Setoid ℓ₀ ℓ₀} {n : ℕ} {m₁ m₂ : Setoid.Carrier (VecISetoid (MaybeSetoid S) at n)} → VecISetoid (MaybeSetoid S) at _ ∋ m₁ ≈ m₂ → MaybeSetoid (VecISetoid S at n) ∋ sequenceV m₁ ≈ sequenceV m₂
sequence-cong {S}                                       VecEq.[]-cong = Setoid.refl (MaybeSetoid (VecISetoid S at _))
sequence-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) with sequenceV xs | sequenceV ys | sequence-cong xs≈ys
sequence-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | just sxs | just sys | just p = MaybeEq.just (VecEq._∷-cong_ x≈y p)
sequence-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | nothing | just sys | ()
sequence-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | just sxs | nothing | ()
sequence-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | nothing | nothing | nothing = Setoid.refl (MaybeSetoid (VecISetoid S at _))
sequence-cong {S}                                       (VecEq._∷-cong_ nothing xs≈ys) = Setoid.refl (MaybeSetoid (VecISetoid S at _))

theorem-2 : (G : Get) → {i : Get.|I| G} → (j : Get.|I| G) → (s : Get.Container G Carrier (Get.|gl₁| G i)) → (v : Vec Carrier (Get.|gl₂| G j)) → (u : Get.Container G (Maybe Carrier) (Get.|gl₁| G j)) → bff G j s v ≡ just u → VecISetoid (MaybeSetoid A.setoid) at _ ∋ Get.get G u ≈ map just v
theorem-2 G {i} j s v u p with (lemma-<$>-just ((flip union (reshape (delete-many (Get.get G (enumerate (Get.ShapeT G) (Get.|gl₁| G i))) (fromFunc (denumerate (Get.ShapeT G) s))) (Get.arity G (Get.|gl₁| G j)))) <$> (assoc (Get.get G (enumerate (Get.ShapeT G) (Get.|gl₁| G j))) v)) p)
theorem-2 G {i} j s v u p | h′ , ph′ with (lemma-<$>-just (assoc (Get.get G (enumerate (Get.ShapeT G) (Get.|gl₁| G j))) v) ph′)
theorem-2 G {i} j s v u p | h′ , ph′ | h , ph = begin⟨ VecISetoid (MaybeSetoid A.setoid) at _ ⟩
  get u
    ≡⟨ just-injective (trans (cong (_<$>_ get) (sym p))
                             (cong (_<$>_ get ∘ _<$>_ h′↦r ∘ _<$>_ h↦h′) ph)) ⟩
  get (h′↦r (h↦h′ h))
    ≡⟨ refl ⟩
  get (fmap (flip lookupM (h↦h′ h)) t)
    ≡⟨ free-theorem (flip lookupM (h↦h′ h)) t ⟩
  map (flip lookupM (h↦h′ h)) (get t)
    ≡⟨ lemma-union-not-used h g′ (get t) (lemma-assoc-domain (get t) v h ph) ⟩
  map (flip lookupM h) (get t)
    ≈⟨ lemma-2 (get t) v h ph ⟩
  map just v ∎
    where open SetoidReasoning
          open Get G
          s′   = enumerate ShapeT (|gl₁| i)
          g    = fromFunc (denumerate ShapeT s)
          g′   = delete-many (get s′) g
          t    = enumerate ShapeT (|gl₁| j)
          h↦h′ = flip union (reshape g′ (arity (|gl₁| j)))
          h′↦r = (λ f → fmap f t) ∘ flip lookupM

theorem-2′ : (G : Get) → {i : Get.|I| G} → (j : Get.|I| G) → (s : Get.Container G Carrier (Get.|gl₁| G i)) → (v : Vec Carrier (Get.|gl₂| G j)) → (u : Get.Container G Carrier (Get.|gl₁| G j)) → bff G j s v ≡ just (Get.fmap G just u) → VecISetoid A.setoid at _ ∋ Get.get G u ≈ v
theorem-2′ G j s v u p = drop-just (begin
  get <$> just u
    ≡⟨ cong (_<$>_ get) (sym (lemma-just-sequence G u)) ⟩
  get <$> sequence (fmap just u)
    ≡⟨ lemma-get-sequence G (lemma-just-sequence G u) ⟩
  sequenceV (get (fmap just u))
    ≈⟨ sequence-cong (theorem-2 G j s v (fmap just u) p) ⟩
  sequenceV (map just v)
    ≡⟨ lemma-just-sequenceV v ⟩
  just v ∎)
  where open EqR (MaybeSetoid (VecISetoid A.setoid at _))
        open Get G
