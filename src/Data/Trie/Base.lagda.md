Basic operations on the ternary finite set.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Data.Trie.Base where

open import Core.Type

open import Data.Trie.Type

ind : ∀ {u} (P : Trie → Type u) → P ll → P mm → P rr → ∀ t → P t
ind P l m r ll = l
ind P l m r mm = m
ind P l m r rr = r
{-# INLINE ind #-}

not : Trie → Trie
not ll = mm
not mm = rr
not rr = ll
{-# INLINE not #-}

flip : Trie → Trie
flip ll = rr
flip mm = mm
flip rr = ll
{-# INLINE flip #-}

min : Trie → Trie → Trie
min ll ll = ll
min ll mm = ll
min ll rr = ll
min mm ll = ll
min mm mm = mm
min mm rr = mm
min rr ll = ll
min rr mm = mm
min rr rr = rr
{-# INLINE min #-}

max : Trie → Trie → Trie
max ll ll = ll
max ll mm = mm
max ll rr = rr
max mm ll = mm
max mm mm = mm
max mm rr = rr
max rr ll = rr
max rr mm = rr
max rr rr = rr
{-# INLINE max #-}

```
