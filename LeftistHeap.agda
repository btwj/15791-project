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
open import Data.Nat as Nat using (_+_; _⊔_; _≤_)
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
join t₁ a t₂ = if rank t₁ ≤ᵇ rank t₂ then ret (node a t₁ t₂) else ret (node a t₂ t₁)

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

if-elim : ∀ {A : Set} {x : A} {b : Bool} → (if b then x else x) ≡ x
if-elim {A} {x} {false} = refl
if-elim {A} {x} {true} = refl

data SortedList : List ℕ → ℕ → Set where
  sorted-nil : ∀ {n : ℕ} → SortedList [] n
  sorted-cons : ∀ {n x x' : ℕ} {xs : List ℕ} → SortedList xs x' → x Nat.≤ x' → n Nat.≤ x → SortedList (x ∷ xs) n

-- we need to strengthen to sorted lists
merge-comm : ∀ {m n : ℕ} (x y : List ℕ) → SortedList x m → SortedList y n → merge' x y ≡ merge' y x
merge-comm ([]) ([]) _ _ = refl
merge-comm ([]) (y ∷ ys) _ _ = refl
merge-comm (x ∷ xs) ([]) _ _ = refl
merge-comm (x ∷ xs) (y ∷ ys) x≥m y≥n with x ≤ᵇ y | Nat.≤ᵇ-reflects-≤ x y | y ≤ᵇ x | Nat.≤ᵇ-reflects-≤ y x
... | true | ofʸ x≤y | false | _ =
    let open ≡-Reasoning in
    begin
      x ∷ merge' xs (y ∷ ys)
    ≡⟨ {!   !} ⟩
      {!   !}
    ∎
... | true | ofʸ x≤y | true | ofʸ y≤x =
    let open ≡-Reasoning in
    begin
      x ∷ merge' xs (y ∷ ys)
    ≡⟨ Eq.cong (λ z → z ∷ merge' xs (y ∷ ys)) (Nat.≤∧≮⇒≡ x≤y (Nat.≤⇒≯ y≤x)) ⟩
      y ∷ merge' xs (y ∷ ys)
    ≡⟨ Eq.cong (λ z → y ∷ merge' xs (z ∷ ys)) (Nat.≤∧≮⇒≡ x≤y (Nat.≤⇒≯ y≤x)) ⟨
      y ∷ merge' xs (x ∷ ys)
    ≡⟨ {!   !} ⟩
      y ∷ merge' ys (x ∷ xs)
    ∎
... | false | _ | true | _ = {!   !}
... | false | _ | false | _ = {!   !}

toList : Tree → List ℕ
toList leaf = []
toList (node x l r) = x ∷ merge' (toList l) (toList r)

-- mergeing two sorted lists gives back another sorted list
merge-sort : ∀ {n₁ n₂ : ℕ} {l₁ l₂ : List ℕ} → SortedList l₁ n₁ → SortedList l₂ n₂ → SortedList (merge' l₁ l₂) (n₁ Nat.⊓ n₂)
merge-sort {l₁ = []} l₁≥n₁ l₂≥n₂ = {!   !}
merge-sort {l₁ = x ∷ l₁} l₁≥n₁ l₂≥n₂ = {!   !}

min-id : ∀ {x : ℕ} → x Nat.≤ x Nat.⊓ x
min-id {Nat.zero} = z≤n
min-id {suc x} = s≤s min-id

toList-sort : {t : Tree} {n : ℕ} → HeapAtLeast t n → SortedList (toList t) n
toList-sort {leaf} {n} h = sorted-nil
toList-sort {node x l r} {n} (minHeapNode l≥x r≥x n≤x) =
  let ls = toList-sort l≥x in
  let rs = toList-sort r≥x in
  let m = merge-sort ls rs in sorted-cons m min-id n≤x

toList-merge-comm : {x : ℕ} (l r : Tree) → HeapAtLeast l _ → HeapAtLeast r _ → toList (node x l r) ≡ toList (node x r l)
toList-merge-comm {x} l r l≥ r≥ = Eq.cong (x ∷_) (merge-comm (toList l) (toList r) (toList-sort l≥) (toList-sort r≥))

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
  ≡⟨ Eq.cong (λ z → bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂)) (λ x → z x)) (funext (λ x → if-elim)) ⟨
    bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
      (λ x →
        if rank l₁ ≤ᵇ rank x
          then ret (toList (node x₁ l₁ x))
          else ret (toList (node x₁ l₁ x)))
  ≡⟨ Eq.cong (λ z → bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂)) (λ x → if rank l₁ ≤ᵇ rank x then ret (toList (node x₁ l₁ x)) else (ret (z x)))) (funext (λ t → toList-merge-comm l₁ t {!   !} {!   !})) ⟩
    bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
      (λ x →
        if rank l₁ ≤ᵇ rank x
          then ret (toList (node x₁ l₁ x))
          else ret (toList (node x₁ x l₁)))
  ≡⟨⟩
    bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
      (λ x →
        if rank l₁ ≤ᵇ rank x
          then bind (F (list nat)) (ret {tree} (node x₁ l₁ x)) (ret ∘ toList)
          else bind (F (list nat)) (ret {tree} (node x₁ x l₁)) (ret ∘ toList))
  ≡⟨ Eq.cong (λ z → bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂)) (λ x → z x)) (funext (λ x → Bool.if-float (λ y → bind (F (list nat)) y (ret {list nat} ∘ toList)) (rank l₁ ≤ᵇ rank x) {x = ret {tree} (node x₁ l₁ x)} {y = ret (node x₁ x l₁)})) ⟨
    bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
      (λ x →
        bind (F (list nat))
        (if rank l₁ ≤ᵇ rank x then ret {tree} (node x₁ l₁ x) else ret (node x₁ x l₁))
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
... | no p | .false | ofⁿ x₁≰x₂ | _ | _ = {!   !} -- symmetric

meld/cost : ∀ (t₁ t₂ : val tree) → WellRanked t₁ → WellRanked t₂ → Σ[ t ∈ Tree ] (meld t₁ t₂ ≤⁺[ U (F tree) ] step (F tree) (rank t₁ Nat.+ rank t₂) (ret t))
meld/cost leaf leaf _ _ =
  leaf ,
  let open ≤⁻-Reasoning (F tree) in
  begin
    ret leaf
  ≡⟨ step/0 {F tree} ⟨
    step (F tree) 0 (ret leaf)
  ∎
meld/cost leaf (node x l r) _ _ =
  (node x l r) ,
  let open ≤⁻-Reasoning (F tree) in
  begin
    ret (node x l r)
  ≡⟨ (step/0 {F tree}) ⟨
    (step (F tree) 0 (ret (node x l r)))
  ≲⟨ step-monoˡ-≤⁻ (ret (node x l r)) z≤n ⟩
    (step (F tree) (rank (node x l r)) (ret (node x l r)))
  ∎
meld/cost (node x l r) leaf _ _ =
  (node x l r) ,
  let open ≤⁻-Reasoning (F tree) in
  begin
    ret (node x l r)
  ≡⟨ (step/0 {F tree}) ⟨
    (step (F tree) 0 (ret (node x l r)))
  ≲⟨ step-monoˡ-≤⁻ (ret (node x l r)) z≤n ⟩
    (step (F tree) (rank r Nat.+ 1 Nat.+ 0) (ret (node x l r)))
  ∎
meld/cost (node x₁ l₁ r₁) (node x₂ l₂ r₂) wr₁ wr₂ with x₁ ≤ᵇ x₂
... | true =
  let open ≤⁻-Reasoning (F tree) in
  begin
    ?
  ≡⟨ ? ⟩
    ?
  ∎
... | false = {!   !}