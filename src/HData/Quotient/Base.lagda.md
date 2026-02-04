Elimination principles for set quotients.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Quotient.Base where

open import HData.Quotient.Type

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Nat using (Nat; S; Z)
open import Core.Trait.Trunc
  using (PathP-is-hlevel; is-prop→is-hlevel-suc; Π-is-prop)

private variable
  u v w : Level
  A B : Type u
  R : A → A → Type v
```


## Recursion

To define a function out of a quotient into a set, we need a function
on the underlying type that respects the relation.

```agda

/-rec : {B : Type w}
      → is-set B
      → (f : A → B)
      → ({a b : A} → R a b → f a ≡ f b)
      → A / R → B
/-rec B-set f f-resp [ a ] = f a
/-rec B-set f f-resp (quot r i) = f-resp r i
/-rec B-set f f-resp (squash/ x y p q i j) =
  B-set (/-rec B-set f f-resp x)
        (/-rec B-set f f-resp y)
        (ap (/-rec B-set f f-resp) p)
        (ap (/-rec B-set f f-resp) q) i j
```


## Induction

For dependent elimination, the type family must land in sets.

```agda

/-elim : {P : A / R → Type w}
       → ((x : A / R) → is-set (P x))
       → (f : (a : A) → P [ a ])
       → ({a b : A} (r : R a b) → PathP (λ i → P (quot r i)) (f a) (f b))
       → (x : A / R) → P x
/-elim P-set f f-resp [ a ] = f a
/-elim P-set f f-resp (quot r i) = f-resp r i
/-elim {P = P} P-set f f-resp (squash/ x y p q i j) =
  is-set→SquareP (λ i j → P (squash/ x y p q i j))
    (λ i j → P-set (squash/ x y p q i j))
    (ap g p) refl (ap g q) refl i j
  where
    g = /-elim P-set f f-resp

    is-set→SquareP
      : (A' : I → I → Type w)
      → ((i j : I) → is-set (A' i j))
      → {a00 : A' i0 i0} {a01 : A' i0 i1}
        {a10 : A' i1 i0} {a11 : A' i1 i1}
      → (p' : PathP (λ j → A' i0 j) a00 a01)
      → (q' : PathP (λ i → A' i i0) a00 a10)
      → (r' : PathP (λ j → A' i1 j) a10 a11)
      → (s' : PathP (λ i → A' i i1) a01 a11)
      → SquareP A' p' q' r' s'
    is-set→SquareP A' A'-set p' q' r' s' =
      is-prop→PathP (λ i → PathP-is-hlevel {n = S Z}
        (A'-set i i1)) p' r'
```


## Two-argument recursion

Useful for defining binary operations on quotients.

```agda

/-rec₂ : {C : Type w}
       → is-set C
       → (f : A → A → C)
       → ({a a' : A} → R a a' → (b : A) → f a b ≡ f a' b)
       → ({b b' : A} → R b b' → (a : A) → f a b ≡ f a b')
       → A / R → A / R → C
/-rec₂ {A = A} {R = R} {C = C} C-set f f-l f-r x y = go x y
  where
    Π-is-set
      : {D : A / R → Type w}
      → ((x' : A / R) → is-set (D x'))
      → is-set ((x' : A / R) → D x')
    Π-is-set dset g h p' q' i j x' =
      dset x' (g x') (h x') (ap (λ f' → f' x') p')
        (ap (λ f' → f' x') q') i j

    go-inner : A → A / R → C
    go-inner a = /-rec C-set (f a) (λ r → f-r r a)

    go-inner-resp
      : {a a' : A} → R a a'
      → (y' : A / R) → go-inner a y' ≡ go-inner a' y'
    go-inner-resp {a} {a'} r =
      /-elim (λ _ → is-prop→is-set (C-set _ _)) (f-l r)
        λ {b} {b'} s → is-prop→PathP
          (λ i → C-set (go-inner a (quot s i))
            (go-inner a' (quot s i)))
          (f-l r b) (f-l r b')

    go : A / R → A / R → C
    go = /-rec (Π-is-set (λ _ → C-set)) go-inner
      (λ r → funext (go-inner-resp r))
```
