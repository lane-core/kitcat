Properties and trait instances for polymorphic binary trees.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Data.Tree.Properties where

open import Core.Type
open import Core.Base using (_≡_; refl; ap; ap2; is-set; funext)
open import Core.Kan using (_∙_)
open import Core.Transport using (subst)
open import Core.Data.Dec using (Dec; yes; no; DecEq)
open Dec using (hedberg)
open import Core.Data.Empty using (⊥)
open import Core.Data.Nat.Type using (Nat; Z; S)

open import Data.Tree.Type
open import Data.Tree.Base

open import Core.Trait.Effect
open import Core.Trait.Map
open import Core.Trait.Foldable hiding (foldr)

private variable
  u v w : Level
  A B C : Type u

```

## Decidable equality

Head extractors recover the recursive argument from each constructor.

```agda

private
  leaf-head : A → Tree A → A
  leaf-head d (leaf a)     = a
  leaf-head d (node _ _)   = d

  node-left : Tree A → Tree A → Tree A
  node-left d (leaf _)     = d
  node-left d (node l _)   = l

  node-right : Tree A → Tree A → Tree A
  node-right d (leaf _)    = d
  node-right d (node _ r)  = r

DecEq-Tree : DecEq A → DecEq (Tree A)
DecEq-Tree _≟_ (leaf a)     (leaf b)     with a ≟ b
... | yes p = yes (ap leaf p)
... | no ¬p = no λ q → ¬p (ap (leaf-head a) q)
DecEq-Tree _≟_ (leaf _)     (node _ _)   = no (λ p → subst f p tt) where f = λ { (leaf _) → ⊤ ; (node _ _) → ⊥ }
DecEq-Tree _≟_ (node _ _)   (leaf _)     = no (λ p → subst f p tt) where f = λ { (leaf _) → ⊥ ; (node _ _) → ⊤ }
DecEq-Tree _≟_ (node l₁ r₁) (node l₂ r₂)
  with DecEq-Tree _≟_ l₁ l₂ | DecEq-Tree _≟_ r₁ r₂
... | yes p | yes q = yes (λ i → node (p i) (q i))
... | yes _ | no ¬q = no λ e → ¬q (ap (node-right r₁) e)
... | no ¬p | _     = no λ e → ¬p (ap (node-left l₁) e)

Tree-is-set : DecEq A → is-set (Tree A)
Tree-is-set d = hedberg (DecEq-Tree d)

```

## Map properties

```agda

module tree-map where
  id-law : (t : Tree A) → tree-map id t ≡ t
  id-law (leaf a)   = refl
  id-law (node l r) i = node (id-law l i) (id-law r i)

  comp-law
    : (f : B → C) (g : A → B) (t : Tree A)
    → tree-map (f ∘ g) t ≡ tree-map f (tree-map g t)
  comp-law f g (leaf a)   = refl
  comp-law f g (node l r) i =
    node (comp-law f g l i) (comp-law f g r i)

```

## Mirror properties

```agda

module mirror where
  invol : (t : Tree A) → mirror (mirror t) ≡ t
  invol (leaf a)   = refl
  invol (node l r) i = node (invol l i) (invol r i)

```

## Trait instances

```agda

instance
  Map-Tree : Map (impl Tree)
  Map-Tree .map = tree-map
  Map-Tree .map-id = funext tree-map.id-law
  Map-Tree .map-comp {f = f} {g} =
    funext (tree-map.comp-law f g)

instance
  Foldable-Tree : Foldable (impl Tree)
  Foldable-Tree .Foldable.foldr = fold

```

## Computational checks

```agda

private
  _ : size (leaf tt) ≡ 0
  _ = refl

  _ : size (node (leaf tt) (leaf tt)) ≡ 1
  _ = refl

  _ : depth (leaf tt) ≡ 0
  _ = refl

  _ : depth (node (leaf tt) (leaf tt)) ≡ 1
  _ = refl

  _ : depth (node (node (leaf tt) (leaf tt)) (leaf tt)) ≡ 2
  _ = refl

  _ : ldepth (leaf tt) ≡ 0
  _ = refl

  _ : ldepth (node (leaf tt) (leaf tt)) ≡ 1
  _ = refl

  _ : ldepth (node (node (leaf tt) (leaf tt)) (leaf tt)) ≡ 2
  _ = refl

  _ : ldepth (node (leaf tt) (node (leaf tt) (leaf tt))) ≡ 1
  _ = refl

```
