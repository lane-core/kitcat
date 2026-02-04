Properties of set quotients: universal property, functorial action,
and examples.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module HData.Quotient.Properties where

open import HData.Quotient.Type
open import HData.Quotient.Base

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Equiv
open import Core.Data.Sigma
open import Core.Data.Nat using (Nat; S; Z)
open import Core.Data.Nat.Base using (_+_; _*_)
open import Core.Trait.Trunc
  using ( PathP-is-hlevel; is-prop→is-hlevel-suc
        ; Π-is-prop; Π-is-hlevel)

private variable
  u v v' w : Level
  A B : Type u
  R : A → A → Type v
```


## Universal property

The quotient satisfies a universal property: for any set `B`, functions
`A / R -> B` correspond bijectively to functions `A -> B` that respect
the relation.

```agda

/-rec-β : {B : Type w} (B-set : is-set B)
        → (f : A → B)
        → (resp : {a b : A} → R a b → f a ≡ f b)
        → (a : A) → /-rec B-set f resp [ a ] ≡ f a
/-rec-β B-set f resp a = refl

/-rec-unique : {B : Type w} (B-set : is-set B)
             → (f : A → B)
             → (resp : {a b : A} → R a b → f a ≡ f b)
             → (g : A / R → B)
             → ((a : A) → g [ a ] ≡ f a)
             → (x : A / R) → g x ≡ /-rec B-set f resp x
/-rec-unique B-set f resp g agree =
  /-elim (λ x → is-prop→is-set (B-set (g x)
    (/-rec B-set f resp x))) agree
    λ {a} {b} r → is-prop→PathP
      (λ i → B-set (g (quot r i)) (resp r i))
      (agree a) (agree b)
```


## Functorial action

```agda

/-map : {A : Type u} {R : A → A → Type v}
        {B : Type u} {S : B → B → Type v'}
      → (f : A → B)
      → ({a b : A} → R a b → S (f a) (f b))
      → A / R → B / S
/-map f resp = /-rec squash/ (λ a → [ f a ]) (λ r → quot (resp r))
```


## Example: integers as a quotient

The integers can be constructed as the quotient of pairs of natural
numbers by the relation `(a, b) ~ (c, d)` when `a + d = c + b`.

```agda

module IntegersExample where
  _~Int_ : (Nat × Nat) → (Nat × Nat) → Type
  (a , b) ~Int (c , d) = a + d ≡ c + b

  Integer : Type
  Integer = (Nat × Nat) / _~Int_

  from-pos : Nat → Integer
  from-pos n = [ n , Z ]

  from-neg : Nat → Integer
  from-neg Z = [ Z , Z ]
  from-neg (S n) = [ Z , S n ]

  private
    open import Core.Data.Nat.Properties using (module add)
    open add using () renaming (assoc to +-assoc; comm to +-comm)

    add : Nat × Nat → Nat × Nat → Integer
    add (a , b) (c , d) = [ a + c , b + d ]

    rearrange-l
      : (a c b' d : Nat)
      → (a + c) + (b' + d) ≡ (a + b') + (c + d)
    rearrange-l a c b' d =
      sym (+-assoc a c (b' + d))
      ∙ ap (a +_) (+-assoc c b' d)
      ∙ ap (λ x → a + (x + d)) (+-comm c b')
      ∙ ap (a +_) (sym (+-assoc b' c d))
      ∙ +-assoc a b' (c + d)

    rearrange-r
      : (a' b c d : Nat)
      → (a' + b) + (c + d) ≡ (a' + c) + (b + d)
    rearrange-r a' b c d =
      sym (+-assoc a' b (c + d))
      ∙ ap (a' +_) (+-assoc b c d)
      ∙ ap (λ x → a' + (x + d)) (+-comm b c)
      ∙ ap (a' +_) (sym (+-assoc c b d))
      ∙ +-assoc a' c (b + d)

    add-resp-l
      : {x x' : Nat × Nat} → x ~Int x'
      → (y : Nat × Nat) → add x y ≡ add x' y
    add-resp-l {a , b} {a' , b'} r (c , d) = quot goal
      where
        goal : (a + c) + (b' + d) ≡ (a' + c) + (b + d)
        goal = rearrange-l a c b' d
          ∙ ap (_+ (c + d)) r
          ∙ rearrange-r a' b c d

    add-resp-r
      : {y y' : Nat × Nat} → y ~Int y'
      → (x : Nat × Nat) → add x y ≡ add x y'
    add-resp-r {c , d} {c' , d'} r (a , b) = quot goal
      where
        step1 : (a + c) + (b + d') ≡ (a + b) + (c + d')
        step1 = rearrange-l a c b d'

        step2 : (a + b) + (c + d') ≡ (a + b) + (c' + d)
        step2 = ap ((a + b) +_) r

        step3 : (a + b) + (c' + d) ≡ (a + c') + (b + d)
        step3 = rearrange-r a b c' d

        goal : (a + c) + (b + d') ≡ (a + c') + (b + d)
        goal = step1 ∙ step2 ∙ step3

  _+Int_ : Integer → Integer → Integer
  _+Int_ = /-rec₂ squash/ add add-resp-l add-resp-r
```
