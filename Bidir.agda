module Bidir where

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
open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality using (cong ; sym ; inspect ; [_] ; _≗_ ; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

open import FinMap
open import CheckInsert

open import BFF using (_>>=_ ; fmap)

open BFF.VecBFF using (get-type ; assoc ; enumerate ; denumerate ; bff)

lemma-1 : {τ : Set} {m n : ℕ} → (eq : EqInst τ) → (f : Fin n → τ) → (is : Vec (Fin n) m) → assoc eq is (map f is) ≡ just (restrict f (toList is))
lemma-1 eq f []        = refl
lemma-1 eq f (i ∷ is′) = begin
  assoc eq (i ∷ is′) (map f (i ∷ is′))
    ≡⟨ refl ⟩
  assoc eq is′ (map f is′) >>= checkInsert eq i (f i)
    ≡⟨ cong (λ m → m >>= checkInsert eq i (f i)) (lemma-1 eq f is′) ⟩
  just (restrict f (toList is′)) >>= (checkInsert eq i (f i))
    ≡⟨ refl ⟩
  checkInsert eq i (f i) (restrict f (toList is′))
    ≡⟨ lemma-checkInsert-restrict eq f i (toList is′) ⟩
  just (restrict f (toList (i ∷ is′))) ∎

lemma-lookupM-assoc : {A : Set} {m n : ℕ} → (eq : EqInst A) → (i : Fin n) → (is : Vec (Fin n) m) → (x : A) → (xs : Vec A m) → (h : FinMapMaybe n A) → assoc eq (i ∷ is) (x ∷ xs) ≡ just h → lookupM i h ≡ just x
lemma-lookupM-assoc eq i is x xs h    p with assoc eq is xs
lemma-lookupM-assoc eq i is x xs h    () | nothing
lemma-lookupM-assoc eq i is x xs h    p | just h' = apply-checkInsertProof eq i x h' record
  { same  = λ lookupM≡justx → begin
      lookupM i h
        ≡⟨ cong (lookupM i) (lemma-from-just (trans (sym p) (lemma-checkInsert-same eq i x h' lookupM≡justx))) ⟩
      lookupM i h'
        ≡⟨ lookupM≡justx ⟩
      just x ∎
  ; new   = λ lookupM≡nothing → begin
      lookupM i h
        ≡⟨ cong (lookupM i) (lemma-from-just (trans (sym p) (lemma-checkInsert-new eq i x h' lookupM≡nothing))) ⟩
      lookupM i (insert i x h')
        ≡⟨ lemma-lookupM-insert i x h' ⟩
      just x ∎
  ; wrong = λ x' x≢x' lookupM≡justx' → lemma-just≢nothing (trans (sym p) (lemma-checkInsert-wrong eq i x h' x' x≢x' lookupM≡justx'))
  }

lemma-∉-lookupM-assoc : {A : Set} {m n : ℕ} → (eq : EqInst A) → (i : Fin n) → (is : Vec (Fin n) m) → (xs : Vec A m) → (h : FinMapMaybe n A) → assoc eq is xs ≡ just h → (i ∉ toList is) → lookupM i h ≡ nothing
lemma-∉-lookupM-assoc eq i []         []         h ph i∉is = begin
  lookupM i h
    ≡⟨ cong (lookupM i) (sym (lemma-from-just ph)) ⟩
  lookupM i empty
    ≡⟨ lemma-lookupM-empty i ⟩
  nothing ∎
lemma-∉-lookupM-assoc eq i (i' ∷ is') (x' ∷ xs') h ph i∉is with assoc eq is' xs' | inspect (assoc eq is') xs'
lemma-∉-lookupM-assoc eq i (i' ∷ is') (x' ∷ xs') h () i∉is | nothing | [ ph' ]
lemma-∉-lookupM-assoc eq i (i' ∷ is') (x' ∷ xs') h ph i∉is | just h' | [ ph' ] = apply-checkInsertProof eq i' x' h' record {
    same = λ lookupM-i'-h'≡just-x' → begin
      lookupM i h
        ≡⟨ cong (lookupM i) (lemma-from-just (trans (sym ph) (lemma-checkInsert-same eq i' x' h' lookupM-i'-h'≡just-x'))) ⟩
      lookupM i h'
        ≡⟨ lemma-∉-lookupM-assoc eq i is' xs' h' ph' (i∉is ∘ there) ⟩
      nothing ∎
  ; new = λ lookupM-i'-h'≡nothing → begin
      lookupM i h
        ≡⟨ cong (lookupM i)  (lemma-from-just (trans (sym ph) (lemma-checkInsert-new eq i' x' h' lookupM-i'-h'≡nothing))) ⟩
      lookupM i (insert i' x' h')
        ≡⟨ sym (lemma-lookupM-insert-other i i' x' h' (i∉is ∘ here)) ⟩
      lookupM i h'
        ≡⟨ lemma-∉-lookupM-assoc eq i is' xs' h' ph' (i∉is ∘ there) ⟩
      nothing ∎
  ; wrong = λ x'' x'≢x'' lookupM-i'-h'≡just-x'' → lemma-just≢nothing (trans (sym ph) (lemma-checkInsert-wrong eq i' x' h' x'' x'≢x'' lookupM-i'-h'≡just-x''))
  }

_in-domain-of_ : {n : ℕ} {A : Set} → (is : List (Fin n)) → (FinMapMaybe n A) → Set
_in-domain-of_ is h = All (λ i → ∃ λ x → lookupM i h ≡ just x) is

lemma-assoc-domain : {m n : ℕ} {A : Set} → (eq : EqInst A) → (is : Vec (Fin n) m) → (xs : Vec A m) → (h : FinMapMaybe n A) → assoc eq is xs ≡ just h → (toList is) in-domain-of h
lemma-assoc-domain eq []         []         h ph = Data.List.All.[]
lemma-assoc-domain eq (i' ∷ is') (x' ∷ xs') h ph with assoc eq is' xs' | inspect (assoc eq is') xs'
lemma-assoc-domain eq (i' ∷ is') (x' ∷ xs') h () | nothing | [ ph' ]
lemma-assoc-domain eq (i' ∷ is') (x' ∷ xs') h ph | just h' | [ ph' ] = apply-checkInsertProof eq i' x' h' record {
    same = λ lookupM-i'-h'≡just-x' → Data.List.All._∷_
      (x' , (trans (cong (lookupM i') (lemma-from-just (trans (sym ph) (lemma-checkInsert-same eq i' x' h' lookupM-i'-h'≡just-x')))) lookupM-i'-h'≡just-x'))
      (lemma-assoc-domain eq is' xs' h (trans ph' (trans (sym (lemma-checkInsert-same eq i' x' h' lookupM-i'-h'≡just-x')) ph)))
  ; new  = λ lookupM-i'-h'≡nothing → Data.List.All._∷_
      (x' , (trans (cong (lookupM i') (lemma-from-just (trans (sym ph) (lemma-checkInsert-new eq i' x' h' lookupM-i'-h'≡nothing)))) (lemma-lookupM-insert i' x' h')))
      (Data.List.All.map
        (λ {i} p → proj₁ p , lemma-lookupM-checkInsert eq i i' (proj₁ p) x' h' h (proj₂ p) ph)
        (lemma-assoc-domain eq is' xs' h' ph'))
  ; wrong = λ x'' x'≢x'' lookupM-i'-h'≡just-x'' → lemma-just≢nothing (trans (sym ph) (lemma-checkInsert-wrong eq i' x' h' x'' x'≢x'' lookupM-i'-h'≡just-x''))
  }

lemma-map-lookupM-insert : {m n : ℕ} {A : Set} → (eq : EqInst A) → (i : Fin n) → (is : Vec (Fin n) m) → (x : A) → (h : FinMapMaybe n A) → i ∉ (toList is) → (toList is) in-domain-of h → map (flip lookupM (insert i x h)) is ≡ map (flip lookupM h) is
lemma-map-lookupM-insert eq i []         x h i∉is ph = refl
lemma-map-lookupM-insert eq i (i' ∷ is') x h i∉is ph = begin
  lookupM i' (insert i x h) ∷ map (flip lookupM (insert i x h)) is'
    ≡⟨ cong (flip _∷_ (map (flip lookupM (insert i x h)) is')) (sym (lemma-lookupM-insert-other i' i x h (i∉is ∘ here ∘ sym))) ⟩
  lookupM i' h ∷ map (flip lookupM (insert i x h)) is'
    ≡⟨ cong (_∷_ (lookupM i' h)) (lemma-map-lookupM-insert eq i is' x h (i∉is ∘ there) (Data.List.All.tail ph)) ⟩
  lookupM i' h ∷ map (flip lookupM h) is' ∎

lemma-map-lookupM-assoc : {m n : ℕ} {A : Set} → (eq : EqInst A) → (i : Fin n) → (is : Vec (Fin n) m) → (x : A) → (xs : Vec A m) → (h : FinMapMaybe n A) → (h' : FinMapMaybe n A) → assoc eq is xs ≡ just h' → checkInsert eq i x h' ≡ just h → map (flip lookupM h) is ≡ map (flip lookupM h') is
lemma-map-lookupM-assoc eq i []         x []         h h' ph' ph = refl
lemma-map-lookupM-assoc eq i (i' ∷ is') x (x' ∷ xs') h h' ph' ph with any (_≟_ i) (toList (i' ∷ is'))
lemma-map-lookupM-assoc eq i (i' ∷ is') x (x' ∷ xs') h h' ph' ph | yes p with Data.List.All.lookup (lemma-assoc-domain eq (i' ∷ is') (x' ∷ xs') h' ph') p
lemma-map-lookupM-assoc eq i (i' ∷ is') x (x' ∷ xs') h h' ph' ph | yes p | (x'' , p') with lookupM i h' 
lemma-map-lookupM-assoc eq i (i' ∷ is') x (x' ∷ xs') h h' ph' ph | yes p | (x'' , refl) | .(just x'') with eq x x''
lemma-map-lookupM-assoc eq i (i' ∷ is') x (x' ∷ xs') h .h ph' refl | yes p | (.x , refl) | .(just x)  | yes refl = refl
lemma-map-lookupM-assoc eq i (i' ∷ is') x (x' ∷ xs') h h' ph' () | yes p | (x'' , refl) | .(just x'') | no ¬p
lemma-map-lookupM-assoc eq i (i' ∷ is') x (x' ∷ xs') h h' ph' ph | no ¬p rewrite lemma-∉-lookupM-assoc eq i (i' ∷ is') (x' ∷ xs') h' ph' ¬p = begin
  map (flip lookupM h) (i' ∷ is')
    ≡⟨ map-cong (λ i'' → cong (lookupM i'') (lemma-from-just (sym ph))) (i' ∷ is') ⟩
  map (flip lookupM (insert i x h')) (i' ∷ is')
    ≡⟨ lemma-map-lookupM-insert eq i (i' ∷ is') x h' ¬p (lemma-assoc-domain eq (i' ∷ is') (x' ∷ xs') h' ph') ⟩
  map (flip lookupM h') (i' ∷ is') ∎

lemma-2 : {τ : Set} {m n : ℕ} → (eq : EqInst τ) → (is : Vec (Fin n) m) → (v : Vec τ m) → (h : FinMapMaybe n τ) → assoc eq is v ≡ just h → map (flip lookupM h) is ≡ map just v
lemma-2 eq []       []       h p = refl
lemma-2 eq (i ∷ is) (x ∷ xs) h p with assoc eq is xs | inspect (assoc eq is) xs
lemma-2 eq (i ∷ is) (x ∷ xs) h () | nothing | _
lemma-2 eq (i ∷ is) (x ∷ xs) h p | just h' | [ ir ] = begin
  map (flip lookupM h) (i ∷ is)
    ≡⟨ refl ⟩
  lookupM i h ∷ map (flip lookupM h) is
    ≡⟨ cong (flip _∷_ (map (flip lookupM h) is)) (lemma-lookupM-assoc eq i is x xs h (begin
      assoc eq (i ∷ is) (x ∷ xs)
        ≡⟨ cong (flip _>>=_ (checkInsert eq i x)) ir ⟩
      checkInsert eq i x h'
        ≡⟨ p ⟩
      just h ∎) ) ⟩
  just x ∷ map (flip lookupM h) is
    ≡⟨  cong (_∷_ (just x)) (lemma-map-lookupM-assoc eq i is x xs h h' ir p) ⟩
  just x ∷ map (flip lookupM h') is
    ≡⟨ cong (_∷_ (just x)) (lemma-2 eq is xs h' ir) ⟩
  just x ∷ map just xs
    ≡⟨ refl ⟩
  map just (x ∷ xs) ∎

postulate
  free-theorem-list-list : {getlen : ℕ → ℕ} → (get : get-type getlen) → {α β : Set} → (f : α → β) → {m : ℕ} → (v : Vec α m) → get (map f v) ≡ map f (get v)

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

theorem-1 : {getlen : ℕ → ℕ} → (get : get-type getlen) → {m : ℕ} {τ : Set} → (eq : EqInst τ) → (s : Vec τ m) → bff get eq s (get s) ≡ just s
theorem-1 get eq s = begin
  bff get eq s (get s)
    ≡⟨ cong (bff get eq s ∘ get) (sym (lemma-map-denumerate-enumerate s)) ⟩
  bff get eq s (get (map (denumerate s) (enumerate s)))
    ≡⟨ cong (bff get eq s) (free-theorem-list-list get (denumerate s) (enumerate s)) ⟩
  bff get eq s (map (denumerate s) (get (enumerate s)))
    ≡⟨ refl ⟩
  fmap (flip map (enumerate s) ∘ flip lookup) (fmap (flip union (fromFunc (denumerate s))) (assoc eq (get (enumerate s)) (map (denumerate s) (get (enumerate s)))))
    ≡⟨ cong (fmap (flip map (enumerate s) ∘ flip lookup) ∘ fmap (flip union (fromFunc (denumerate s)))) (lemma-1 eq (denumerate s) (get (enumerate s))) ⟩
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

theorem-2 : {getlen : ℕ → ℕ} (get : get-type getlen) → {τ : Set} {m : ℕ} → (eq : EqInst τ) → (v : Vec τ (getlen m)) → (s u : Vec τ m) → bff get eq s v ≡ just u → get u ≡ v
theorem-2 get eq v s u p with lemma-fmap-just (assoc eq (get (enumerate s)) v) (proj₂ (lemma-fmap-just (fmap (flip union (fromFunc (denumerate s))) (assoc eq (get (enumerate s)) v)) p))
theorem-2 get eq v s u p | h , ph = begin
  get u
    ≡⟨ lemma-from-just (begin
      just (get u)
        ≡⟨ refl ⟩
      fmap get (just u)
        ≡⟨ cong (fmap get) (sym p) ⟩
      fmap get (bff get eq s v)
        ≡⟨ cong (fmap get ∘ fmap (flip map (enumerate s) ∘ flip lookup) ∘ fmap (flip union (fromFunc (denumerate s)))) ph ⟩
      fmap get (fmap (flip map (enumerate s) ∘ flip lookup) (fmap (flip union (fromFunc (denumerate s))) (just h)))
       ≡⟨ refl ⟩
     just (get (map (flip lookup (union h (fromFunc (denumerate s)))) (enumerate s)))
       ∎) ⟩
  get (map (flip lookup (union h (fromFunc (denumerate s)))) (enumerate s))
    ≡⟨ free-theorem-list-list get (flip lookup (union h (fromFunc (denumerate s)))) (enumerate s) ⟩
  map (flip lookup (union h (fromFunc (denumerate s)))) (get (enumerate s))
     ≡⟨ lemma-from-map-just (begin
       map just (map (flip lookup (union h (fromFunc (denumerate s)))) (get (enumerate s)))
         ≡⟨ lemma-union-not-used h (fromFunc (denumerate s)) (get (enumerate s)) (lemma-assoc-domain eq (get (enumerate s)) v h ph) ⟩
       map (flip lookupM h) (get (enumerate s))
         ≡⟨ lemma-2 eq (get (enumerate s)) v h ph ⟩
       map just v
         ∎) ⟩
  v ∎
