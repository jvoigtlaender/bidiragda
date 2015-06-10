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
open import Instances using (MaybeFunctor ; ShapedISetoid)
import GetTypes
open GetTypes.PartialShapeShape using (Get ; module Get)
open import Generic using (mapMV ; mapMV-cong ; mapMV-purity ; sequenceV ; VecISetoid ; just-injective)
open import FinMap
import CheckInsert
open CheckInsert A
import BFF
open BFF.PartialShapeBFF A using (assoc ; enumerate ; denumerate ; bff)
open Setoid using () renaming (_≈_ to _∋_≈_)
open module A = DecSetoid A using (Carrier) renaming (_≟_ to deq)

lemma-1 : {m n : ℕ} → (f : Fin n → Carrier) → (is : Vec (Fin n) m) → assoc is (map f is) ≡ just (restrict f is)
lemma-1 f []        = refl
lemma-1 f (i ∷ is′) = begin
  (assoc is′ (map f is′) >>= checkInsert i (f i))
    ≡⟨ cong (λ m → m >>= checkInsert i (f i)) (lemma-1 f is′) ⟩
  checkInsert i (f i) (restrict f is′)
    ≡⟨ lemma-checkInsert-restrict f i is′ ⟩
  just (restrict f (i ∷ is′)) ∎
  where open ≡-Reasoning

lemma-lookupM-checkInserted : {n : ℕ} → (i : Fin n) → (x : Carrier) → (h : FinMapMaybe n Carrier) → {h' : FinMapMaybe n Carrier} → checkInsert i x h ≡ just h' → MaybeSetoid A.setoid ∋ lookupM i h' ≈ just x
lemma-lookupM-checkInserted i x h p with checkInsert i x h | insertionresult i x h
lemma-lookupM-checkInserted i x h refl | ._ | same x' x≈x' pl = begin
  lookupM i h
    ≡⟨ pl ⟩
  just x'
    ≈⟨ MaybeEq.just (Setoid.sym A.setoid x≈x') ⟩
  just x ∎
  where open EqR (MaybeSetoid A.setoid)
lemma-lookupM-checkInserted i x h refl | ._ | new _ = Setoid.reflexive (MaybeSetoid A.setoid) (lemma-lookupM-insert i x h)
lemma-lookupM-checkInserted i x h () | ._ | wrong _ _ _

_in-domain-of_ : {m n : ℕ} {A : Set} → (is : Vec (Fin m) n) → (FinMapMaybe m A) → Set
_in-domain-of_ is h = All (λ i → ∃ λ x → lookupM i h ≡ just x) (toList is)

lemma-assoc-domain : {m n : ℕ} → (is : Vec (Fin n) m) → (xs : Vec Carrier m) → {h : FinMapMaybe n Carrier} → assoc is xs ≡ just h → is in-domain-of h
lemma-assoc-domain []         []         ph = Data.List.All.[]
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') ph with assoc is' xs' | inspect (assoc is') xs'
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') () | nothing | [ ph' ]
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') ph | just h' | [ ph' ] with checkInsert i' x' h' | inspect (checkInsert i' x') h' | insertionresult i' x' h'
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') refl | just h | [ ph' ] | ._ | _ | same x _ pl = All._∷_ (x , pl) (lemma-assoc-domain is' xs' ph')
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') refl | just h' | [ ph' ] | ._ | [ cI≡ ] | new _ = All._∷_
  (x' , lemma-lookupM-insert i' x' h')
  (Data.List.All.map
    (λ {i} p → proj₁ p , lemma-lookupM-checkInsert i i' h' (proj₂ p) x' cI≡)
    (lemma-assoc-domain is' xs' ph'))
lemma-assoc-domain (i' ∷ is') (x' ∷ xs') () | just h' | [ ph' ] | ._ | _ | wrong _ _ _

lemma-map-lookupM-assoc : {m : ℕ} → (i : Fin m) → (x : Carrier) → (h : FinMapMaybe m Carrier) → {h' : FinMapMaybe m Carrier} → checkInsert i x h ≡ just h' → {n : ℕ} → (js : Vec (Fin m) n) → js in-domain-of h → map (flip lookupM h') js ≡ map (flip lookupM h) js
lemma-map-lookupM-assoc i x h ph [] pj = refl
lemma-map-lookupM-assoc i x h ph (j ∷ js) (Data.List.All._∷_ (x' , pl) pj) = cong₂ _∷_
  (trans (lemma-lookupM-checkInsert j i h pl x ph) (sym pl))
  (lemma-map-lookupM-assoc i x h ph js pj)

lemma-2 : {m n : ℕ} → (is : Vec (Fin n) m) → (v : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc is v ≡ just h → VecISetoid (MaybeSetoid A.setoid) at _ ∋ map (flip lookupM h) is ≈ map just v
lemma-2 []       []       h p = ISetoid.refl (VecISetoid (MaybeSetoid A.setoid))
lemma-2 (i ∷ is) (x ∷ xs) h p with assoc is xs | inspect (assoc is) xs
lemma-2 (i ∷ is) (x ∷ xs) h () | nothing | _
lemma-2 (i ∷ is) (x ∷ xs) h p | just h' | [ ir ] = begin
  lookupM i h ∷ map (flip lookupM h) is
    ≈⟨ VecEq._∷-cong_ (lemma-lookupM-checkInserted i x h' p) (ISetoid.refl (VecISetoid (MaybeSetoid A.setoid))) ⟩
  just x ∷ map (flip lookupM h) is
    ≡⟨  cong (_∷_ (just x)) (lemma-map-lookupM-assoc i x h' p is (lemma-assoc-domain is xs ir)) ⟩
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


theorem-1 : (G : Get) → {i : Get.I G} → (s : Get.SourceContainer G Carrier (Get.gl₁ G i)) → bff G i s (Get.get G s) ≡ just (Get.fmapS G just s)
theorem-1 G {i} s = begin
  bff G i s (get s)
    ≡⟨ cong (bff G i s ∘ get) (sym (lemma-fmap-denumerate-enumerate SourceShapeT s)) ⟩
  bff G i s (get (fmapS f t))
    ≡⟨ cong (bff G i s) (free-theorem f t) ⟩
  bff G i s (fmapV f (get t))
    ≡⟨ refl ⟩
  h′↦r <$> (h↦h′ <$> (assoc (Shaped.content ViewShapeT (get t)) (Shaped.content ViewShapeT (fmapV f (get t)))))
    ≡⟨ cong (_<$>_ h′↦r ∘ _<$>_ h↦h′ ∘ assoc (Shaped.content ViewShapeT (get t))) (Shaped.fmap-content ViewShapeT f (get t)) ⟩
  h′↦r <$> (h↦h′ <$> (assoc (Shaped.content ViewShapeT (get t)) (map f (Shaped.content ViewShapeT (get t)))))
    ≡⟨ cong (_<$>_ h′↦r ∘ _<$>_ h↦h′) (lemma-1 f (Shaped.content ViewShapeT (get t))) ⟩
  (Maybe.just ∘ h′↦r ∘ h↦h′) (restrict f (Shaped.content ViewShapeT (get t)))
    ≡⟨ cong just (begin
      h′↦r (union (restrict f (Shaped.content ViewShapeT (get t))) (reshape g′ (Shaped.arity SourceShapeT (gl₁ i))))
        ≡⟨ cong (h′↦r ∘ union (restrict f (Shaped.content ViewShapeT (get t)))) (lemma-reshape-id g′) ⟩
      h′↦r (union (restrict f (Shaped.content ViewShapeT (get t))) g′)
        ≡⟨ cong h′↦r (lemma-disjoint-union f (Shaped.content ViewShapeT (get t))) ⟩
      h′↦r (fromFunc f)
        ≡⟨ refl ⟩
      fmapS (flip lookupM (fromFunc f)) t
        ≡⟨ IsFunctor.cong (Shaped.isFunctor SourceShapeT (gl₁ i)) (lemma-lookupM-fromFunc f) t ⟩
      fmapS (Maybe.just ∘ f) t
        ≡⟨ IsFunctor.composition (Shaped.isFunctor SourceShapeT (gl₁ i)) just f t ⟩
      fmapS just (fmapS f t)
        ≡⟨ cong (fmapS just) (lemma-fmap-denumerate-enumerate SourceShapeT s) ⟩
      fmapS just s ∎) ⟩ _ ∎
    where open ≡-Reasoning
          open Get G
          t    = enumerate SourceShapeT (gl₁ i)
          f    = denumerate SourceShapeT s
          g′   = delete-many (Shaped.content ViewShapeT (get t)) (fromFunc f)
          h↦h′ = flip union (reshape g′ (Shaped.arity SourceShapeT (gl₁ i)))
          h′↦r = (λ f′ → fmapS f′ t) ∘ flip lookupM


lemma-<$>-just : {A B : Set} {f : A → B} {b : B} (ma : Maybe A) → f <$> ma ≡ just b → ∃ λ a → ma ≡ just a
lemma-<$>-just (just x) f<$>ma≡just-b = x , refl
lemma-<$>-just nothing  ()

lemma-union-not-used : {m n : ℕ} {A : Set} (h h' : FinMapMaybe n A) → (is : Vec (Fin n) m) → is in-domain-of h → map (flip lookupM (union h h')) is ≡ map (flip lookupM h) is
lemma-union-not-used         h h' []        p = refl
lemma-union-not-used {n = n} h h' (i ∷ is') (Data.List.All._∷_ (x , px) p') = cong₂ _∷_ (begin
      lookupM i (union h h')
        ≡⟨ lookup∘tabulate (λ j → maybe′ just (lookupM j h') (lookupM j h)) i ⟩
      maybe′ just (lookupM i h') (lookupM i h)
        ≡⟨ cong (maybe′ just (lookupM i h')) px ⟩
      maybe′ just (lookupM i h') (just x)
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

lemma-just-sequence : {S : Set} {C : Set → S → Set} → (ShapeT : Shaped S C) → {A : Set} {s : S} → (c : C A s) → Shaped.sequence ShapeT (Shaped.fmap ShapeT just c) ≡ just c
lemma-just-sequence ShapeT {s = s} c = begin
  fill s <$> sequenceV (content (fmap just c))
    ≡⟨ cong (_<$>_ (fill s) ∘ sequenceV) (fmap-content just c) ⟩
  fill s <$> sequenceV (map just (content c))
    ≡⟨ cong (_<$>_ (fill s)) (lemma-just-sequenceV (content c)) ⟩
  fill s <$> just (content c)
    ≡⟨ cong just (content-fill c) ⟩
  just c ∎
  where open ≡-Reasoning
        open Shaped ShapeT

lemma-sequenceV-successful : {A : Set} {n : ℕ} → (v : Vec (Maybe A) n) → {r : Vec A n} → sequenceV v ≡ just r → v ≡ map just r
lemma-sequenceV-successful []             {r = []}       p = refl
lemma-sequenceV-successful (just x ∷ xs)                 p with sequenceV xs | inspect sequenceV xs
lemma-sequenceV-successful (just x ∷ xs)                 () | nothing | _
lemma-sequenceV-successful (just x ∷ xs)  {r = .x ∷ .ys} refl  | just ys | [ p′ ] = cong (_∷_ (just x)) (lemma-sequenceV-successful xs p′)
lemma-sequenceV-successful (nothing ∷ xs)                ()

lemma-sequence-successful : {S : Set} {C : Set → S → Set} → (ShapeT : Shaped S C) → {A : Set} {s : S} → (c : C (Maybe A) s) → {r : C A s} → Shaped.sequence ShapeT c ≡ just r → c ≡ Shaped.fmap ShapeT just r
lemma-sequence-successful ShapeT {s = s} c {r} p = just-injective (sym (begin
  fill s <$> (map just <$> (content <$> just r))
    ≡⟨ cong (_<$>_ (fill s) ∘ _<$>_ (map just)) (begin
      content <$> just r
        ≡⟨ cong (_<$>_ content) (sym p) ⟩
      content <$> (fill s <$> sequenceV (content c))
        ≡⟨ sym (Functor.composition MaybeFunctor content (fill s) (sequenceV (content c))) ⟩
      content ∘ fill s <$> sequenceV (content c)
        ≡⟨ Functor.cong MaybeFunctor (fill-content s) (sequenceV (content c)) ⟩
      id <$> sequenceV (content c)
        ≡⟨ Functor.identity MaybeFunctor (sequenceV (content c)) ⟩
      sequenceV (content c)
        ≡⟨ cong sequenceV (lemma-sequenceV-successful (content c) (proj₂ wp)) ⟩
      sequenceV (map just (proj₁ wp))
        ≡⟨ lemma-just-sequenceV (proj₁ wp) ⟩
      just (proj₁ (lemma-<$>-just (sequenceV (content c)) p)) ∎) ⟩
  fill s <$> (map just <$> just (proj₁ (lemma-<$>-just (sequenceV (content c)) p)))
    ≡⟨ cong (_<$>_ (fill s) ∘ just) (sym (lemma-sequenceV-successful (content c) (proj₂ wp))) ⟩
  fill s <$> just (content c)
    ≡⟨ cong just (content-fill c) ⟩
  just c ∎))
  where open ≡-Reasoning
        open Shaped ShapeT
        wp = lemma-<$>-just (sequenceV (content c)) p

module _ (G : Get) where
  open ≡-Reasoning
  open Get G
  open Shaped SourceShapeT using () renaming (sequence to sequenceSource)
  open Shaped ViewShapeT using () renaming (sequence to sequenceView)

  lemma-get-sequence : {A : Set} → {i : I} {v : SourceContainer (Maybe A) (gl₁ i)} {r : SourceContainer A (gl₁ i)} → sequenceSource v ≡ just r → get <$> sequenceSource v ≡ sequenceView (get v)
  lemma-get-sequence {v = v} {r = r} p = begin
    get <$> sequenceSource v
      ≡⟨ cong (_<$>_ get ∘ sequenceSource) (lemma-sequence-successful SourceShapeT v p) ⟩
    get <$> sequenceSource (fmapS just r)
      ≡⟨ cong (_<$>_ get) (lemma-just-sequence SourceShapeT r) ⟩
    get <$> just r
      ≡⟨ sym (lemma-just-sequence ViewShapeT (get r)) ⟩
    sequenceView (fmapV just (get r))
      ≡⟨ cong sequenceView (sym (free-theorem just r)) ⟩
    sequenceView (get (fmapS just r))
      ≡⟨ cong (sequenceView ∘ get) (sym (lemma-sequence-successful SourceShapeT v p)) ⟩
    sequenceView (get v) ∎

sequenceV-cong : {S : Setoid ℓ₀ ℓ₀} {n : ℕ} {m₁ m₂ : Setoid.Carrier (VecISetoid (MaybeSetoid S) at n)} → VecISetoid (MaybeSetoid S) at _ ∋ m₁ ≈ m₂ → MaybeSetoid (VecISetoid S at n) ∋ sequenceV m₁ ≈ sequenceV m₂
sequenceV-cong {S}                                       VecEq.[]-cong = Setoid.refl (MaybeSetoid (VecISetoid S at _))
sequenceV-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) with sequenceV xs | sequenceV ys | sequenceV-cong xs≈ys
sequenceV-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | just sxs | just sys | just p = MaybeEq.just (VecEq._∷-cong_ x≈y p)
sequenceV-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | nothing | just sys | ()
sequenceV-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | just sxs | nothing | ()
sequenceV-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | nothing | nothing | nothing = Setoid.refl (MaybeSetoid (VecISetoid S at _))
sequenceV-cong {S}                                       (VecEq._∷-cong_ nothing xs≈ys) = Setoid.refl (MaybeSetoid (VecISetoid S at _))

sequence-cong : {S : Set} {C : Set → S → Set} → (ShapeT : Shaped S C) → (α : Setoid ℓ₀ ℓ₀) → {s : S} {x y : C (Maybe (Setoid.Carrier α)) s} → ShapedISetoid (EqSetoid S) ShapeT (MaybeSetoid α) at _ ∋ x ≈ y → MaybeSetoid (ShapedISetoid (EqSetoid S) ShapeT α at _) ∋ Shaped.sequence ShapeT x ≈ Shaped.sequence ShapeT y
sequence-cong ShapeT α {x = x} {y = y} (shape≈ , content≈) with sequenceV (Shaped.content ShapeT x) | sequenceV (Shaped.content ShapeT y) | sequenceV-cong content≈
sequence-cong ShapeT α {s} (shape≈ , content≈) | .(just x) | .(just y) | just {x} {y} x≈y = just (refl , (begin
  content (fill s x)
    ≡⟨ fill-content s x ⟩
  x
    ≈⟨ x≈y ⟩
  y
    ≡⟨ sym (fill-content s y) ⟩
  content (fill s y) ∎))
  where open EqR (VecISetoid α at _)
        open Shaped ShapeT
sequence-cong ShapeT α (shape≈ , content≈) | .nothing  | .nothing  | nothing = nothing

module _ (G : Get) where
  open Get G
  open Shaped SourceShapeT using () renaming (arity to arityS)
  open Shaped ViewShapeT using () renaming (content to contentV)

  theorem-2 : {i : I} → (j : I) → (s : SourceContainer Carrier (gl₁ i)) → (v : ViewContainer Carrier (gl₂ j)) → (u : SourceContainer (Maybe Carrier) (gl₁ j)) → bff G j s v ≡ just u → ShapedISetoid (EqSetoid _) ViewShapeT (MaybeSetoid A.setoid) at _ ∋ get u ≈ Get.fmapV G just v
  theorem-2 {i} j s v u p with lemma-<$>-just ((flip union (reshape (delete-many (contentV (get (enumerate SourceShapeT (gl₁ i)))) (fromFunc (denumerate SourceShapeT s))) (arityS (gl₁ j)))) <$> assoc (contentV (get (enumerate SourceShapeT (gl₁ j)))) (contentV v)) p
  theorem-2 {i} j s v u p | h′ , ph′ with lemma-<$>-just (assoc (contentV (get (enumerate SourceShapeT (gl₁ j)))) (contentV v)) ph′
  theorem-2 {i} j s v u p | h′ , ph′ | h , ph = refl , (begin
    contentV (get u)
      ≡⟨ cong contentV (just-injective (trans (cong (_<$>_ get) (sym p))
                                              (cong (_<$>_ get ∘ _<$>_ h′↦r ∘ _<$>_ h↦h′) ph))) ⟩
    contentV (get (h′↦r (h↦h′ h)))
      ≡⟨ refl ⟩
    contentV (get (fmapS (flip lookupM (h↦h′ h)) t))
      ≡⟨ cong contentV (free-theorem (flip lookupM (h↦h′ h)) t) ⟩
    contentV (fmapV (flip lookupM (h↦h′ h)) (get t))
      ≡⟨ Shaped.fmap-content ViewShapeT (flip lookupM (h↦h′ h)) (get t) ⟩
    map (flip lookupM (h↦h′ h)) (contentV (get t))
      ≡⟨ lemma-union-not-used h (reshape g′ (arityS (gl₁ j))) (contentV (get t)) (lemma-assoc-domain (contentV (get t)) (contentV v) ph) ⟩
    map (flip lookupM h) (contentV (get t))
      ≈⟨ lemma-2 (contentV (get t)) (contentV v) h ph ⟩
    map just (contentV v)
      ≡⟨ sym (Shaped.fmap-content ViewShapeT just v) ⟩
    contentV (fmapV just v) ∎)
      where open EqR (VecISetoid (MaybeSetoid A.setoid) at _)
            s′   = enumerate SourceShapeT (gl₁ i)
            g    = fromFunc (denumerate SourceShapeT s)
            g′   = delete-many (contentV (get s′)) g
            t    = enumerate SourceShapeT (gl₁ j)
            h↦h′ = flip union (reshape g′ (arityS (gl₁ j)))
            h′↦r = (λ f → fmapS f t) ∘ flip lookupM

module _ (G : Get) where
  open Get G

  theorem-2′ : {i : I} → (j : I) → (s : SourceContainer Carrier (gl₁ i)) → (v : ViewContainer Carrier (gl₂ j)) → (u : SourceContainer Carrier (gl₁ j)) → bff G j s v ≡ just (Get.fmapS G just u) → ShapedISetoid (EqSetoid _) ViewShapeT A.setoid at _ ∋ get u ≈ v
  theorem-2′ j s v u p = drop-just (begin
    get <$> just u
      ≡⟨ cong (_<$>_ get) (sym (lemma-just-sequence SourceShapeT u)) ⟩
    get <$> Shaped.sequence SourceShapeT (fmapS just u)
      ≡⟨ lemma-get-sequence G (lemma-just-sequence SourceShapeT u) ⟩
    Shaped.sequence ViewShapeT (get (fmapS just u))
      ≈⟨ sequence-cong ViewShapeT A.setoid (theorem-2 G j s v (fmapS just u) p) ⟩
    Shaped.sequence ViewShapeT (fmapV just v)
      ≡⟨ lemma-just-sequence ViewShapeT v ⟩
    just v ∎)
    where open EqR (MaybeSetoid (ShapedISetoid (EqSetoid _) ViewShapeT A.setoid at _))
