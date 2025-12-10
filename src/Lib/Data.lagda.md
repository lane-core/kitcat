# Lib.Data

Fundamental data types with disciplined namespace management.

**Philosophy:**
- Constructors public for ergonomics (write `S (S Z)` naturally)
- Combinators/eliminators qualified to avoid pollution (use `Nat.ind`)
- High bar for public exports to keep namespace clean

**Public (unqualified):**
- Nat constructors: `Z`, `S`
- Σ operations: `Σ`, `_,_`, `fst`, `snd`, `_×_`

**Qualified access required:**
- Nat combinators: `Nat.ind`, `Nat.add`, `Nat.mul`, `Nat.IndOrd.*`
- Sigma utilities: `Sigma.diag`, `Sigma.swap`

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Lib.Data where

open import Lib.Type

-- Qualified module re-exports
module Nat = Lib.Nat
module Sigma = Lib.Sigma

-- Natural numbers: constructors public, combinators qualified
open Lib.Nat public
  using ( Z      -- Zero constructor
        ; S      -- Successor constructor
        )
-- Qualified: Nat.ind, Nat.add, Nat.mul, Nat.monus, Nat._<₂_, Nat.IndOrd

-- Sigma types: fundamental operations public, utilities qualified
open Lib.Sigma public
  using ( Σ      -- Dependent sum type former
        ; _,_    -- Pair constructor
        ; fst    -- First projection
        ; snd    -- Second projection
        ; _×_    -- Non-dependent product
        )
-- Qualified: Sigma.diag, Sigma.swap

```
