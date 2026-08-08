The displayed carrier over the chosen edge: every type of the sequent
vocabulary replaced by its displayed counterpart over a basepoint in
each fiber, the base argument left visible so the displayed one
determines it. `reflect[_]` is the only field beyond the three
structural ones; the displaced actions, injections, and argument
vocabulary are its projections, exactly as the base ones are
`reflect`'s.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Degenerate.Displaced where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Degenerate.Chosen
open import Bb.VirtualGraphs.Degenerate.Lens using (module lens)
open lens using (inj⁻; inj⁺)
```

## The record

```agda
module _ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (idn : (x : ob) → hom x x) where

  open chosen G idn using (var; covar; act-π; coact-π)

  record virtual-graphᴰ (o' h' : Level) : Type₊ (o ⊔ h ⊔ o' ⊔ h') where
    field
      ob[_]  : ob → Type o'
      hom[_] : ∀ {x y} → hom x y → ob[ x ] → ob[ y ] → Type h'
      idn[_] : ∀ {x} (x' : ob[ x ]) → hom[ idn x ] x' x'

    term[_] : ∀ {x} (t : term x) → ob[ x ] → Type (o' ⊔ h')
    term[ t ] x' = Σ w' ∶ ob[ t .fst ] , hom[ t .snd ] w' x'

    coterm[_] : ∀ {y} (e : coterm y) → ob[ y ] → Type (o' ⊔ h')
    coterm[ e ] y' = Σ v' ∶ ob[ e .fst ] , hom[ e .snd ] y' v'

    argument[_] : ∀ {x y} (γ : argument x y) → ob[ x ] → ob[ y ] → Type (o' ⊔ h')
    argument[ γ ] x' y' = term[ γ .fst ] x' × coterm[ γ .snd ] y'

    conclusion[_] : ∀ {x y} {γ : argument x y} → conclusion γ
                  → ∀ {x' y'} → argument[ γ ] x' y' → Type h'
    conclusion[ c ] γ' = hom[ c ] (γ' .fst .fst) (γ' .snd .fst)

    judgment[_] : ∀ {x y} → judgment x y → ob[ x ] → ob[ y ] → Type (o ⊔ h ⊔ o' ⊔ h')
    judgment[ α ] x' y' = ∀ γ (γ' : argument[ γ ] x' y') → conclusion[ α γ ] γ'

    field
      reflect[_] : ∀ {x y} {f : hom x y} {x' y'}
                 → hom[ f ] x' y' → judgment[ reflect f ] x' y'
```

Every displaced action and injection follows from `reflect[_]`
exactly as the base one follows from `reflect`.

```agda
    var[_] : ∀ {a} (a' : ob[ a ]) → term[ var a ] a'
    var[ a' ] = a' , idn[ a' ]

    covar[_] : ∀ {y} (y' : ob[ y ]) → coterm[ covar y ] y'
    covar[ y' ] = y' , idn[ y' ]

    act-π[_] : ∀ {x y} {f : hom x y} {x' y'} → hom[ f ] x' y'
             → ∀ {t : term x} (t' : term[ t ] x')
             → hom[ act-π f t ] (t' .fst) y'
    act-π[_] {y' = y'} f' t' = reflect[ f' ] _ (t' , covar[ y' ])

    coact-π[_] : ∀ {x y} {f : hom x y} {x' y'} → hom[ f ] x' y'
               → ∀ {e : coterm y} (e' : coterm[ e ] y')
               → hom[ coact-π f e ] x' (e' .fst)
    coact-π[_] {x' = x'} f' e' = reflect[ f' ] _ (var[ x' ] , e')

    inj⁻[_] : ∀ {x y z} {α : judgment x y} {x' y'} → judgment[ α ] x' y'
            → ∀ {p : hom y z} {z'} → hom[ p ] y' z'
            → judgment[ inj⁻ G idn α p ] x' z'
    inj⁻[ α' ] p' _ γ' = α' _ (γ' .fst , (γ' .snd .fst , coact-π[ p' ] (γ' .snd)))

    inj⁺[_] : ∀ {x y z} {p : hom x y} {x' y'} → hom[ p ] x' y'
            → ∀ {β : judgment y z} {z'} → judgment[ β ] y' z'
            → judgment[ inj⁺ G idn p β ] x' z'
    inj⁺[ p' ] β' _ γ' = β' _ ((γ' .fst .fst , act-π[ p' ] (γ' .fst)) , γ' .snd)
```

## What the record is not

`Bb.VirtualGraphs.Degenerate.Lens`'s displays are indexed by base objects, and
their vertices *are* judgments. `judgment[_]` is indexed by a base
judgment together with a displayed object over each endpoint, and its
elements are displayed conclusions over the base ones — a different
family, at a different index. The lens display is the vertex family
of a transport structure; `virtual-graphᴰ` is Σ-by-Σ, with
`reflect[_]` the single field and every displaced action and
injection its projection.
