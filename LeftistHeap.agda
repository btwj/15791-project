{-# OPTIONS --rewriting --prop --guardedness #-}

module LeftistHeap where

open import Algebra.Cost

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.Parallel parCostMonoid
open import Calf.Data.Bool
open import Calf.Data.Nat
open import Calf.Data.List
open import Calf.Data.Maybe
open import Calf.Data.Product
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.BigO costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Nat as Nat using (_+_; _⊔_; _<_)

data Tree : Set where
  leaf : Tree
  node : val nat → Tree → Tree → Tree

_<ᶜ_ : cmp (Π nat λ _ → Π nat λ _ → F bool)
x <ᶜ y = step (F bool) (1 , 1) (ret (x <ᵇ y))

tree : tp⁺
tree = meta⁺ Tree

rank : Tree → ℕ
rank leaf = 0
rank (node x l r) = rank r + 1

join : cmp (Π tree λ _ → Π nat λ _ → Π tree λ _ → F tree)
join t₁ a t₂ = if rank t₁ <ᵇ rank t₂ then ret (node a t₁ t₂) else ret (node a t₂ t₁)

meld : cmp (Π tree λ _ → Π tree λ _ → F tree)
meld leaf t = ret t
meld t leaf = ret t
meld (node x₁ l₁ r₁) (node x₂ l₂ r₂) = bind (F tree) (x₁ <ᶜ x₂)
  λ b →
    if b
    then
      bind (F tree) (meld r₁ (node x₂ l₂ r₂)) (λ r' → join l₁ x₁ r')
    else
      bind (F tree) (meld (node x₁ l₁ r₁) r₂) (λ r' → join l₂ x₂ r')

pop : cmp (Π tree λ _ → F (maybe (nat ×⁺ tree)))
pop (leaf) = ret nothing
pop (node x l r) = bind (F (maybe (nat ×⁺ tree))) (meld l r) λ t → ret (just (x , t))

-- ∀h. rank(left(h)) ≥ rank(right(h))
data WellRanked : Tree → Set where
  wellRankedLeaf : WellRanked leaf
  wellRankedNode : ∀ {l r : Tree}{x : val nat} → WellRanked l → WellRanked r → WellRanked (node x l r)

minOpt : val nat → Maybe (val nat) → val nat
minOpt x nothing = x
minOpt x (just y) = if x <ᵇ y then x else y

min2Opt : val nat → Maybe (val nat) → Maybe (val nat) → val nat
min2Opt x y z = minOpt (minOpt x y) z

root : Tree → Maybe (val nat)
root leaf = nothing
root (node x l r) = just x

-- Min-Heap Property: ∀h. (left(h) ≠ E ⇒ value(h) ≤ value(left(h))) ∧ (right(h) ≠ E ⇒ value(h) ≤ value(right(h)))
data MinHeap : Tree → Set where
  minHeapLeaf : MinHeap leaf
  minHeapNode : ∀ {l r : Tree}{x : val nat} → MinHeap l → MinHeap r → min2Opt x (root l) (root r) ≡ x → MinHeap (node x l r)

merge' : List ℕ → List ℕ → List ℕ
merge' [] x = x
merge' x [] = x
merge' (x ∷ xs) (y ∷ ys) =
  if x <ᵇ y then x ∷ merge' xs (y ∷ ys) else y ∷ merge' (x ∷ xs) ys

toList : cmp (Π tree λ _ → F (list nat))
toList leaf = ret []
toList (node x l r) = bind (F (list nat)) (toList l) (λ l' → bind (F (list nat)) (toList r) (λ r' → ret (x ∷ merge' l' r')))

-- toListHIsSorted : ∀ {h : Tree} → sorted (toList h)

-- Correctness 
-- properMeld : ∀ {h₁ h₂ : val tree} → toList (meld h₁ h₂) ≡ merge ? (toList h₁) (toList h₂)
ProperMeld : cmp (Π tree λ _ → Π tree λ _ → F tree) → Set
ProperMeld meld = (t₁ t₂ : Tree) → (mh₁ : MinHeap t₁) → (mh₂ : MinHeap t₂) → (wr₁ : WellRanked t₁) → (wr₂ : WellRanked t₂) →
  ◯ (bind (F (list nat)) (toList t₁) (λ l₁ →
    bind (F (list nat)) (toList t₂) (λ l₂ → ret (merge' l₁ l₂)))
  ≡ bind (F (list nat)) (meld t₁ t₂) (λ t →
    bind (F (list nat)) (toList t) ret))

meld/correct : ProperMeld meld
meld/correct leaf t _ _ _ _ = λ u → refl
meld/correct t leaf _ _ _ _ = λ u →
  let open ≡-Reasoning in
  begin
    bind (F (list nat)) (toList t) (λ l₁ → ret (merge' l₁ []))
  ≡⟨ Eq.cong (λ x → bind (F (list nat)) (toList t) x) (funext λ l → refl) ⟩
    bind (F (list nat)) (toList t) (ret)
  ≡⟨ bind/η ⟩
    toList t
  ≡⟨ Eq.sym bind/β  ⟩
    bind (F (list nat)) (ret t) (λ t₁ → toList t₁)
  ≡⟨⟩
    bind (F (list nat)) (meld t leaf) (λ t₁ → toList t₁)
  ∎
meld/correct (node x₁ l₁ r₁) (node x₂ l₂ r₂) mh₁ mh₂ wr₁ wr₂ with x₁ <ᵇ x₂
... | true = λ u →
        let open ≡-Reasoning in
        begin
          bind (F (list nat)) (toList l₁)
            (λ a →
              bind (F (list nat)) (toList r₁)
              (λ a₁ →
                  bind (F (list nat)) (toList l₂)
                  (λ a₂ →
                    bind (F (list nat)) (toList r₂)
                    (λ a₃ → ret (x₁ ∷ merge' (merge' a a₁) (x₂ ∷ merge' a₂ a₃))))))
        ≡⟨ {!   !} ⟩
          step
          (F (list nat)) (1 , 1)
          (bind (F (list nat)) (meld r₁ (node x₂ l₂ r₂))
          (λ a →
              bind (F (list nat))
              (if rank l₁ <ᵇ rank a then ret (node x₁ l₁ a) else ret (node x₁ a l₁))
              (λ z → toList z)))
        ∎ 
... | false = {!   !}

  -- λ u →
  -- let open ≡-Reasoning in
  -- begin
  --   bind (F (list nat)) (toList l₁)
  --     (λ a →
  --        bind (F (list nat)) (toList r₁)
  --        (λ a₁ →
  --           bind (F (list nat)) (toList l₂)
  --           (λ a₂ →
  --              bind (F (list nat)) (toList r₂)
  --              (λ a₃ →
  --                 ret
  --                 (if x₁ <ᵇ x₂ then x₁ ∷ merge' (merge' a a₁) (x₂ ∷ merge' a₂ a₃)
  --                  else x₂ ∷ merge' (x₁ ∷ merge' a a₁) (merge' a₂ a₃))))))
  -- ≡⟨ {!   !} ⟩
  --   step (F (list nat)) (1 , 1)
  --     (bind (F (list nat))
  --      (if x₁ <ᵇ x₂ then
  --       bind (F tree) (meld r₁ (node x₂ l₂ r₂)) (join l₁ x₁) else
  --       bind (F tree) (meld (node x₁ l₁ r₁) r₂) (join l₂ x₂))
  --      (λ z → toList z))
  -- ∎ 