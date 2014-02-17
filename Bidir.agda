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
open import Data.Vec using (Vec ; [] ; _∷_ ; toList ; map ; tabulate) renaming (lookup to lookupVec)
open import Data.Vec.Equality using () renaming (module Equality to VecEq)
open import Data.Vec.Properties using (tabulate-∘ ; lookup∘tabulate ; map-cong ; map-∘)
open import Data.Product using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Function using (id ; _∘_ ; flip)
open import Relation.Binary.Core using (refl ; _≡_)
open import Relation.Binary.Indexed using (_at_) renaming (Setoid to ISetoid)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; [_] ; trans ; cong₂ ; decSetoid ; module ≡-Reasoning) renaming (setoid to EqSetoid)
open import Relation.Binary using (Setoid ; module Setoid ; module DecSetoid)
import Relation.Binary.EqReasoning as EqR

import GetTypes
open GetTypes.VecVec using (Get ; module Get)
open import Generic using (mapMV ; mapMV-cong ; mapMV-purity ; sequenceV ; sequence-map ; VecISetoid)
open import FinMap
import CheckInsert
open CheckInsert A
import BFF
open BFF.VecBFF A using (assoc ; enumerate ; enumeratel ; denumerate ; bff)
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

lemma-lookupM-assoc : {m n : ℕ} → (i : Fin n) → (is : Vec (Fin n) m) → (x : Carrier) → (xs : Vec Carrier m) → (h : FinMapMaybe n Carrier) → assoc (i ∷ is) (x ∷ xs) ≡ just h → MaybeSetoid A.setoid ∋ lookupM i h ≈ just x
lemma-lookupM-assoc i is x xs h    p with assoc is xs
lemma-lookupM-assoc i is x xs h    () | nothing
lemma-lookupM-assoc i is x xs h    p | just h' with checkInsert i x h' | insertionresult i x h'
lemma-lookupM-assoc i is x xs .h refl | just h | ._ | same x' x≈x' pl = begin
  lookupM i h
    ≡⟨ pl ⟩
  just x'
    ≈⟨ MaybeEq.just (Setoid.sym A.setoid x≈x') ⟩
  just x ∎
  where open EqR (MaybeSetoid A.setoid)
lemma-lookupM-assoc i is x xs ._ refl | just h' | ._ | new _ =  Setoid.reflexive (MaybeSetoid A.setoid) (lemma-lookupM-insert i x h')
lemma-lookupM-assoc i is x xs h () | just h' | ._ | wrong _ _ _

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
    ≈⟨ VecEq._∷-cong_ (lemma-lookupM-assoc i is x xs h (trans (cong (flip _>>=_ (checkInsert i x)) ir) p)) (ISetoid.refl (VecISetoid (MaybeSetoid A.setoid))) ⟩
  just x ∷ map (flip lookupM h) is
    ≡⟨  cong (_∷_ (just x)) (lemma-map-lookupM-assoc i x h h' p is (lemma-assoc-domain is xs h' ir)) ⟩
  just x ∷ map (flip lookupM h') is
    ≈⟨ VecEq._∷-cong_ (Setoid.refl (MaybeSetoid A.setoid)) (lemma-2 is xs h' ir) ⟩
  just x ∷ map just xs ∎
  where open EqR (VecISetoid (MaybeSetoid A.setoid) at _)

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
  where open ≡-Reasoning

theorem-1 : (G : Get) → {m : ℕ} → (s : Vec Carrier m) → bff G m s (Get.get G s) ≡ just s
theorem-1 G {m} s = begin
  bff G m s (get s)
    ≡⟨ cong (bff G m s ∘ get) (sym (lemma-map-denumerate-enumerate s)) ⟩
  bff G m s (get (map (denumerate s) (enumerate s)))
    ≡⟨ cong (bff G m s) (free-theorem (denumerate s) (enumerate s)) ⟩
  bff G m s (map (denumerate s) (get (enumerate s)))
    ≡⟨ refl ⟩
  (h′↦r ∘ h↦h′) (assoc (get (enumerate s)) (map (denumerate s) (get (enumerate s))))
    ≡⟨ cong (h′↦r ∘ h↦h′) (lemma-1 (denumerate s) (get (enumerate s))) ⟩
  (h′↦r ∘ h↦h′ ∘ just) (restrict (denumerate s) (toList (get (enumerate s))))
    ≡⟨ refl ⟩
  (h′↦r ∘ just) (union (restrict (denumerate s) (toList (get (enumerate s)))) (reshape (delete-many (get (enumerate s)) (fromFunc (denumerate s))) m))
    ≡⟨ cong (h′↦r ∘ Maybe.just ∘ union (restrict (denumerate s) (toList (get (enumerate s))))) (lemma-reshape-id (delete-many (get (enumerate s)) (fromFunc (denumerate s)))) ⟩
  (h′↦r ∘ just) (union (restrict (denumerate s) (toList (get (enumerate s)))) (delete-many (get (enumerate s)) (fromFunc (denumerate s))))
    ≡⟨ cong (h′↦r ∘ just) (lemma-disjoint-union (denumerate s) (get (enumerate s))) ⟩
  (h′↦r ∘ just) (fromFunc (denumerate s))
    ≡⟨ refl ⟩
  mapMV (flip lookupM (fromFunc (denumerate s))) (enumerate s)
    ≡⟨ mapMV-cong (lemma-lookupM-fromFunc (denumerate s)) (enumerate s) ⟩
  mapMV (Maybe.just ∘ denumerate s) (enumerate s)
    ≡⟨ mapMV-purity (denumerate s) (enumerate s) ⟩
  just (map (denumerate s) (enumerate s))
    ≡⟨ cong just (lemma-map-denumerate-enumerate s) ⟩
  just s ∎
    where open ≡-Reasoning
          open Get G
          h↦h′ = _<$>_ (flip union (reshape (delete-many (get (enumerate s)) (fromFunc (denumerate s))) m))
          h′↦r = flip _>>=_ (flip mapMV (enumerate s) ∘ flip lookupM)


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

lemma-just-sequence : {A : Set} {n : ℕ} → (v : Vec A n) → sequenceV (map just v) ≡ just v
lemma-just-sequence []       = refl
lemma-just-sequence (x ∷ xs) = cong (_<$>_ (_∷_ x)) (lemma-just-sequence xs)

lemma-mapM-successful : {A B : Set} {f : A → Maybe B} {n : ℕ} → (v : Vec A n) → {r : Vec B n} → mapMV f v ≡ just r → ∃ λ w → map f v ≡ map just w
lemma-mapM-successful         []      p = [] , refl
lemma-mapM-successful {f = f} (x ∷ xs) p with f x | mapMV f xs | inspect (mapMV f) xs
lemma-mapM-successful         (x ∷ xs) () | nothing | _ | _
lemma-mapM-successful         (x ∷ xs) () | just y | nothing | _
lemma-mapM-successful         (x ∷ xs) p  | just y | just ys | [ p′ ] with lemma-mapM-successful xs p′
lemma-mapM-successful         (x ∷ xs) p  | just y | just ys | [ p′ ] | w , pw = y ∷ w , cong (_∷_ (just y)) pw


lemma-get-mapMV : {A B : Set} {f : A → Maybe B} {n : ℕ} {v : Vec A n} {r : Vec B n} → mapMV f v ≡ just r → (get : Get) → Get.get get <$> mapMV f v ≡ mapMV f (Get.get get v)
lemma-get-mapMV {f = f} {v = v} p G = begin
  get <$> mapMV f v
    ≡⟨ cong (_<$>_ get) (sym (sequence-map f v)) ⟩
  get <$> (sequenceV (map f v))
    ≡⟨ cong (_<$>_ get ∘ sequenceV) (proj₂ wp) ⟩
  get <$> (sequenceV (map just (proj₁ wp)))
    ≡⟨ cong (_<$>_ get) (lemma-just-sequence (proj₁ wp)) ⟩
  get <$> just (proj₁ wp)
    ≡⟨ sym (lemma-just-sequence (get (proj₁ wp))) ⟩
  sequenceV (map just (get (proj₁ wp)))
    ≡⟨ cong sequenceV (sym (free-theorem just (proj₁ wp))) ⟩
  sequenceV (get (map just (proj₁ wp)))
    ≡⟨ cong (sequenceV ∘ get) (sym (proj₂ wp)) ⟩
  sequenceV (get (map f v))
    ≡⟨ cong sequenceV (free-theorem f v) ⟩
  sequenceV (map f (get v))
    ≡⟨ sequence-map f (get v) ⟩
  mapMV f (get v) ∎
  where open ≡-Reasoning
        open Get G
        wp = lemma-mapM-successful v p

sequence-cong : {S : Setoid ℓ₀ ℓ₀} {n : ℕ} {m₁ m₂ : Setoid.Carrier (VecISetoid (MaybeSetoid S) at n)} → VecISetoid (MaybeSetoid S) at _ ∋ m₁ ≈ m₂ → MaybeSetoid (VecISetoid S at n) ∋ sequenceV m₁ ≈ sequenceV m₂
sequence-cong {S}                                       VecEq.[]-cong = Setoid.refl (MaybeSetoid (VecISetoid S at _))
sequence-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) with sequenceV xs | sequenceV ys | sequence-cong xs≈ys
sequence-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | just sxs | just sys | just p = MaybeEq.just (VecEq._∷-cong_ x≈y p)
sequence-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | nothing | just sys | ()
sequence-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | just sxs | nothing | ()
sequence-cong {S} {m₁ = just x ∷ xs} {m₂ = just y ∷ ys} (VecEq._∷-cong_ (just x≈y) xs≈ys) | nothing | nothing | nothing = Setoid.refl (MaybeSetoid (VecISetoid S at _))
sequence-cong {S}                                       (VecEq._∷-cong_ nothing xs≈ys) = Setoid.refl (MaybeSetoid (VecISetoid S at _))

theorem-2 : (G : Get) → {m : ℕ} → (n : ℕ) → (s : Vec Carrier m) → (v : Vec Carrier (Get.getlen G n)) → (u : Vec Carrier n) → bff G n s v ≡ just u → VecISetoid A.setoid at _ ∋ Get.get G u ≈ v
theorem-2 G n s v u p with (lemma->>=-just ((flip union (reshape (delete-many (Get.get G (enumerate s)) (fromFunc (denumerate s))) n)) <$> (assoc (Get.get G (enumeratel n)) v)) p)
theorem-2 G n s v u p | h′ , ph′ with (lemma-<$>-just (assoc (Get.get G (enumeratel n)) v) ph′)
theorem-2 G n s v u p | h′ , ph′ | h , ph = drop-just (begin⟨ MaybeSetoid (VecISetoid A.setoid at _) ⟩
  get <$> (just u)
    ≡⟨ cong (_<$>_ get) (sym p) ⟩
  get <$> (bff G n s v)
    ≡⟨ cong (_<$>_ get ∘ flip _>>=_ h′↦r ∘ _<$>_ h↦h′) ph ⟩
  get <$> mapMV (flip lookupM (h↦h′ h)) t
    ≡⟨ lemma-get-mapMV (trans (cong (flip _>>=_ h′↦r ∘ _<$>_ h↦h′) (sym ph)) p) G ⟩
  mapMV (flip lookupM (h↦h′ h)) (get t)
    ≡⟨ sym (sequence-map (flip lookupM (h↦h′ h)) (get t)) ⟩
  sequenceV (map (flip lookupM (h↦h′ h)) (get t))
    ≡⟨ cong sequenceV (lemma-union-not-used h g′ (get t) (lemma-assoc-domain (get t) v h ph)) ⟩
  sequenceV (map (flip lookupM h) (get t))
    ≈⟨ sequence-cong (lemma-2 (get t) v h ph) ⟩
  sequenceV (map just v)
    ≡⟨ lemma-just-sequence v ⟩
  just v ∎)
    where open SetoidReasoning
          open Get G
          s′   = enumerate s
          g    = fromFunc (denumerate s)
          g′   = delete-many (get s′) g
          t    = enumeratel n
          h↦h′ = flip union (reshape g′ n)
          h′↦r = flip mapMV t ∘ flip lookupM
