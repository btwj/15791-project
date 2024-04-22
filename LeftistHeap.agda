{-# OPTIONS --rewriting --prop --guardedness #-}

module LeftistHeap where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid

open import Function
open import Relation.Nullary
open import Calf costMonoid
open import Calf.Data.Bool
open import Calf.Data.Nat
open import Calf.Data.List
open import Calf.Data.Maybe
open import Calf.Data.Product
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.BigO costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Nat as Nat using (_+_; _⊔_; _<_)
import Data.Nat.Properties as Nat
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥-elim)

data Tree : Set where
  leaf : Tree
  node : val nat → Tree → Tree → Tree

_≤ᶜ_ : cmp (Π nat λ _ → Π nat λ _ → F bool)
x ≤ᶜ y = step (F bool) 1 (ret (x ≤ᵇ y))

tree : tp⁺
tree = meta⁺ Tree

rank : Tree → ℕ
rank leaf = 0
rank (node x l r) = rank r Nat.+ 1

join : cmp (Π tree λ _ → Π nat λ _ → Π tree λ _ → F tree)
join t₁ a t₂ = if rank t₁ <ᵇ rank t₂ then ret (node a t₁ t₂) else ret (node a t₂ t₁)

meld : cmp (Π tree λ _ → Π tree λ _ → F tree)
meld leaf t = ret t
meld t leaf = ret t
meld (node x₁ l₁ r₁) (node x₂ l₂ r₂) = bind (F tree) (x₁ ≤ᶜ x₂)
  λ b →
    if b
    then
      bind (F tree) (meld r₁ (node x₂ l₂ r₂)) (λ r' → join l₁ x₁ r')
    else
      bind (F tree) (meld (node x₁ l₁ r₁) r₂) (λ r' → join l₂ x₂ r')

meld-idʳ : ∀ {t : Tree} → meld t leaf ≡ ret t
meld-idʳ {leaf} = refl
meld-idʳ {node x t t₁} = refl

pop : cmp (Π tree λ _ → F (maybe (nat ×⁺ tree)))
pop (leaf) = ret nothing
pop (node x l r) = bind (F (maybe (nat ×⁺ tree))) (meld l r) λ t → ret (just (x , t))

-- ∀h. rank(left(h)) ≥ rank(right(h))
data WellRanked : Tree → Set where
  wellRankedLeaf : WellRanked leaf
  wellRankedNode : ∀ {l r : Tree}{x : val nat} → WellRanked l → WellRanked r → rank r Nat.≤ rank l → WellRanked (node x l r)

minOpt : val nat → Maybe (val nat) → val nat
minOpt x nothing = x
minOpt x (just y) = if x <ᵇ y then x else y

min2Opt : val nat → Maybe (val nat) → Maybe (val nat) → val nat
min2Opt x y z = minOpt (minOpt x y) z

root : Tree → Maybe (val nat)
root leaf = nothing
root (node x l r) = just x

-- Min-Heap Property: ∀h. (left(h) ≠ E ⇒ value(h) ≤ value(left(h))) ∧ (right(h) ≠ E ⇒ value(h) ≤ value(right(h)))
data HeapAtLeast : Tree → ℕ → Set where
  minHeapLeaf : ∀ {n : ℕ} → HeapAtLeast leaf n
  minHeapNode : ∀ {l r : Tree} {x x' : val nat} → HeapAtLeast l x → HeapAtLeast r x → x' Nat.≤ x → HeapAtLeast (node x l r) x'

foo : Tree
foo = node 1 (node 2 (node 4 leaf leaf) (node 5 leaf leaf)) (node 3 leaf leaf)

fooWellRanked : WellRanked foo
fooWellRanked = wellRankedNode (wellRankedNode (wellRankedNode wellRankedLeaf wellRankedLeaf z≤n) (wellRankedNode wellRankedLeaf wellRankedLeaf z≤n) (s≤s z≤n)) (wellRankedNode wellRankedLeaf wellRankedLeaf z≤n) (s≤s z≤n)

MinHeap : Tree → Set
MinHeap t = HeapAtLeast t 0

fooHeapAtLeast : HeapAtLeast foo 1
fooHeapAtLeast = minHeapNode (minHeapNode (minHeapNode minHeapLeaf minHeapLeaf (s≤s (s≤s z≤n))) (minHeapNode minHeapLeaf minHeapLeaf (s≤s (s≤s z≤n))) (s≤s z≤n)) (minHeapNode minHeapLeaf minHeapLeaf (s≤s z≤n)) (s≤s z≤n)

merge' : List ℕ → List ℕ → List ℕ
merge' = merge Nat._≤?_

ifElim : ∀ {A : Set} {x : A} {b : Bool} → (if b then x else x) ≡ x
ifElim {A} {x} {false} = refl
ifElim {A} {x} {true} = refl

mergeComm : ∀ {x y : List ℕ} → merge' x y ≡ merge' y x
mergeComm {[]} {[]} = refl
mergeComm {[]} {y ∷ ys} = refl
mergeComm {x ∷ xs} {[]} = refl
mergeComm {x ∷ xs} {y ∷ ys} with x Nat.≤? y | x ≤ᵇ y | Nat.≤ᵇ-reflects-≤ x y
... | yes p | .true | ofʸ x≤y =
        let open ≡-Reasoning in
        begin
          x ∷ merge' xs (y ∷ ys)
        ≡⟨ Eq.cong (x ∷_) (mergeComm {xs} {y ∷ ys}) ⟩
          x ∷ merge' (y ∷ ys) xs
        ≡⟨ {! refl  !} ⟩
          (if y ≤ᵇ x then (y ∷ merge' ys (x ∷ xs)) else (x ∷ merge' (y ∷ ys) xs))
        ≡⟨⟩
          merge' (y ∷ ys) (x ∷ xs)
        ∎
... | yes p | .false | ofⁿ ¬a = ⊥-elim (¬a p)
... | no p | .false | ofⁿ _ = {!   !}
... | no p | .true | ofʸ a = ⊥-elim (p a)

toList : Tree → List ℕ
toList leaf = []
toList (node x l r) = x ∷ merge' (toList l) (toList r)

toListMergeComm : {x : ℕ} (l r : Tree) → toList (node x l r) ≡ toList (node x r l)
toListMergeComm {x} l r = Eq.cong (x ∷_) (mergeComm {toList l} {toList r})

-- toListHIsSorted : ∀ {h : Tree} → sorted (toList h)

-- Correctness 
-- properMeld : ∀ {h₁ h₂ : val tree} → toList (meld h₁ h₂) ≡ merge ? (toList h₁) (toList h₂)
ProperMeld : cmp (Π tree λ _ → Π tree λ _ → F tree) → Set
ProperMeld meld = ∀ {n₁ n₂ : ℕ} (t₁ t₂ : Tree) → HeapAtLeast t₁ n₁ → HeapAtLeast t₂ n₂ →
  ◯ (ret (merge' (toList t₁) (toList t₂)) ≡ bind (F (list nat)) (meld t₁ t₂) (ret ∘ toList))

merge-idʳ : (l : List ℕ) → merge' l [] ≡ l
merge-idʳ [] = refl
merge-idʳ (x ∷ l) = refl

merge-assoc : ∀ (x y z : List ℕ) → merge' (merge' x y) z ≡ merge' x (merge' y z)
merge-assoc [] y z = refl
merge-assoc (x ∷ xs) [] z = refl
merge-assoc (x ∷ xs) (y ∷ ys) [] =
  let open ≡-Reasoning in
  begin
    merge' (merge' (x ∷ xs) (y ∷ ys)) []
  ≡⟨ merge-idʳ (merge' (x ∷ xs) (y ∷ ys)) ⟩
    merge' (x ∷ xs) (y ∷ ys)
  ≡⟨ Eq.cong (merge' (x ∷ xs)) (merge-idʳ (y ∷ ys)) ⟩
    merge' (x ∷ xs) (merge' (y ∷ ys) [])
  ∎
merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) with y Nat.≤? z | x Nat.≤? y
... | yes y≤z | yes x≤y =
  let open ≡-Reasoning in
  begin
    merge' (merge' (x ∷ xs) (y ∷ ys)) (z ∷ zs)
  ≡⟨ {!   !} ⟩
    merge' (x ∷ xs) (y ∷ merge' ys (z ∷ zs))
  ≡⟨ {!   !} ⟩
    merge' (x ∷ xs) (merge' (y ∷ ys) (z ∷ zs))
  ∎
... | yes y≤z | no x≤y = {!   !}
... | no ¬y≤z | yes x≤y = {!   !}
... | no ¬y≤z | no ¬x≤y = {!   !}

meld/correct : ProperMeld meld
meld/correct leaf t _ _ u = refl
meld/correct t leaf _ _ u =
    let open ≡-Reasoning in
    begin
      ret (merge' (toList t) [])
    ≡⟨ Eq.cong ret (merge-idʳ (toList t)) ⟩
      ret (toList t)
    ≡⟨⟩
      bind (F (list nat)) (ret {tree} t) (ret ∘ toList)
    ≡⟨ Eq.cong (λ x → bind (F (list nat)) x (ret ∘ toList)) (meld-idʳ {t}) ⟨
      bind (F (list nat)) (meld t leaf) (ret ∘ toList)
    ∎
meld/correct (node x₁ l₁ r₁) (node x₂ l₂ r₂) mh₁ mh₂ u with x₁ Nat.≤? x₂ | x₁ ≤ᵇ x₂ | Nat.≤ᵇ-reflects-≤ x₁ x₂ | mh₁ | mh₂
... | yes p | .true | ofʸ x₁≤x₂ | minHeapNode l₁≥x₁ r₁≥x₁ n₁≤x₁ | minHeapNode l₂≥x₂ r₂≥x₂ n₂≤x₂ =
  let open ≡-Reasoning in
  begin
    ret
      (x₁ ∷ merge' (merge' (toList l₁) (toList r₁))
        (x₂ ∷ merge' (toList l₂) (toList r₂)))
  ≡⟨ Eq.cong (λ z → ret (x₁ ∷ z)) (merge-assoc (toList l₁) (toList r₁) (toList (node x₂ l₂ r₂))) ⟩
    ret (x₁ ∷ merge' (toList l₁) (merge' (toList r₁) (toList (node x₂ l₂ r₂))))
  ≡⟨⟩
    bind (F (list nat))
      (ret {list nat} (merge' (toList r₁) (toList (node x₂ l₂ r₂))))
      (λ res → ret (x₁ ∷ merge' (toList l₁) res))  
  ≡⟨ Eq.cong (λ x → bind (F (list nat)) x (λ res → ret (x₁ ∷ merge' (toList l₁) res))) (meld/correct r₁ (node x₂ l₂ r₂) r₁≥x₁ mh₂ u) ⟩  -- cite IH
    bind (F (list nat))
      (bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂)) (ret ∘ toList))
      (λ res → ret (x₁ ∷ merge' (toList l₁) res))  
  ≡⟨⟩
    bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
      (λ x → ret (x₁ ∷ merge' (toList l₁) (toList x)))  
  ≡⟨⟩
    bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
      (λ x → ret (toList (node x₁ l₁ x)))  -- ???
  ≡⟨ Eq.cong (λ z → bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂)) (λ x → z x)) (funext (λ x → ifElim)) ⟨
    bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
      (λ x →
        if rank l₁ <ᵇ rank x
          then ret (toList (node x₁ l₁ x))
          else ret (toList (node x₁ l₁ x)))
  ≡⟨ Eq.cong (λ z → bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂)) (λ x → if rank l₁ <ᵇ rank x then ret (toList (node x₁ l₁ x)) else (ret (z x)))) (funext (toListMergeComm l₁)) ⟩
    bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
      (λ x →
        if rank l₁ <ᵇ rank x
          then ret (toList (node x₁ l₁ x))
          else ret (toList (node x₁ x l₁)))
  ≡⟨⟩
    bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
      (λ x →
        if rank l₁ <ᵇ rank x
          then bind (F (list nat)) (ret {tree} (node x₁ l₁ x)) (ret ∘ toList)
          else bind (F (list nat)) (ret {tree} (node x₁ x l₁)) (ret ∘ toList))
  ≡⟨ Eq.cong (λ z → bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂)) (λ x → z x)) (funext (λ x → Bool.if-float (λ y → bind (F (list nat)) y (ret {list nat} ∘ toList)) (rank l₁ <ᵇ rank x) {x = ret {tree} (node x₁ l₁ x)} {y = ret (node x₁ x l₁)})) ⟨
    bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
      (λ x →
        bind (F (list nat))
        (if rank l₁ <ᵇ rank x then ret {tree} (node x₁ l₁ x) else ret (node x₁ x l₁))
        (ret ∘ toList))
  ≡⟨⟩
    bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
      (λ a₁ →
        bind (F (list nat))
        (join l₁ x₁ a₁)
        (ret ∘ toList))
  ≡⟨ step/ext (F (list nat)) ((bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂)) (λ a₁ → bind (F (list nat)) (join l₁ x₁ a₁) (ret ∘ toList)))) 1 u ⟨
    step (F (list nat)) 1
      (bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
       (λ a₁ →
          bind (F (list nat))
          (join l₁ x₁ a₁)
          (ret ∘ toList)))
  ∎
... | yes p | .false | ofⁿ ¬a | _ | _ = ⊥-elim (¬a p)
... | no p | .true | ofʸ a | _ | _ = ⊥-elim (p a) 
... | no p | .false | ofⁿ ¬a | _ | _ = {!   !} -- symmetric?