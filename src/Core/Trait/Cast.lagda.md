Perform a (potentially lossy!) cast operation (from Idris2)

You are expected to name your instance after the types being converted
between. This naming convention is semantically based; so for a cast
between is-prop and is-contr you would name your instance
`is-prop→is-contr`.  This is so that it will display as `cast
is-prop→is-contr` in displayed syntax.

There is an expected interface to implement when making an instance
for this record.  If I have a source `S` and a target `T` which needs
some data for T, say its some A, then your cast would be to `Cast S (A
→ T)`. Calling cast will therefore give you the function requesting
the auxillary data sufficient to reach the target.

```
{-# OPTIONS --safe --cubical-compatible #-}

module Core.Trait.Cast where

open import Core.Type

record Cast {u v} (S : Type u) (T : Type v) : Typeω where
  no-eta-equality
  field
    cast : S → T

open Cast ⦃ ... ⦄ public
```
