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
  where
    join : cmp (Π tree λ _ → Π nat λ _ → Π tree λ _ → F tree)
    join t₁ a t₂ = if rank t₁ <ᵇ rank t₂ then ret (node a t₁ t₂) else ret (node a t₂ t₁)

pop : cmp (Π tree λ _ → F (maybe (nat ×⁺ tree)))
pop (leaf) = ret nothing
pop (node x l r) = bind (F (maybe (nat ×⁺ tree))) (meld l r) λ t → ret (just (x , t))   