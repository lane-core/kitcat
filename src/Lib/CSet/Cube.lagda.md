The connection-free cube category. Morphisms are bare functions
`Fin n -> Fin m ⊎ Bool`, representing substitutions that map
variables to either variables or constant endpoints.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.CSet.Cube where

open import Core.Data.Nat
open import Core.Data.Fin.Type
open import Core.Data.Fin.Base hiding (weaken)
open import Core.Data.Fin.Properties using (fin-path)
open import Core.Data.Fin.Monotone using (weaken; restrict; fpred)
open import Core.Data.Empty
open import Core.Data.Sum
open import Core.Data.Bool
open import Core.Type
open import Core.Base
open import Core.Kan using (_∙_)

open Nat

private variable
  m n k l : Nat

```

## Cube maps

A cube map `m ⇒□ n` represents a morphism [m] -> [n] in the
cube category. Each coordinate of the target n-cube maps to
either a variable of the source m-cube or a constant endpoint.

The function direction matches the simplex category convention:
morphisms go from target `Fin n` to source. Unlike simplices,
cube maps can send coordinates to constant endpoints (`inr b`),
not just source variables.

```agda

_⇒□_ : Nat -> Nat -> Type
m ⇒□ n = Fin n -> Fin m ⊎ Bool

infix 5 _⇒□_

```

## Identity and composition

```agda

id□ : n ⇒□ n
id□ j = inl j

private
  -- Kleisli extension for (_⊎ Bool): apply substitution
  -- to variables, keep endpoints fixed.
  subst-expr
    : Fin m ⊎ Bool
    -> (Fin m -> Fin n ⊎ Bool)
    -> Fin n ⊎ Bool
  subst-expr (inl i) f = f i
  subst-expr (inr b) f = inr b

comp□ : m ⇒□ k -> n ⇒□ m -> n ⇒□ k
comp□ g f j = subst-expr (g j) f

{-# INLINE comp□ #-}

```

## Diagrammatic composition

```agda

private
  _⨾□_ : n ⇒□ m -> m ⇒□ k -> n ⇒□ k
  f ⨾□ g = comp□ g f

  infixr 9 _⨾□_

```

## Category laws

```agda

comp□-idl : (f : m ⇒□ n) -> comp□ id□ f ≡ f
comp□-idl f = refl

comp□-idr : (f : m ⇒□ n) -> comp□ f id□ ≡ f
comp□-idr f = funext pw where
  pw : (j : _) -> comp□ f id□ j ≡ f j
  pw j with f j
  ... | inl i = refl
  ... | inr b = refl

comp□-assoc
  : (h : k ⇒□ l) (g : m ⇒□ k) (f : n ⇒□ m)
  -> comp□ (comp□ h g) f ≡ comp□ h (comp□ g f)
comp□-assoc h g f = funext pw where
  pw : (j : _) -> comp□ (comp□ h g) f j
     ≡ comp□ h (comp□ g f) j
  pw j with h j
  ... | inl i = refl
  ... | inr b = refl

```

## Skip map

Order-preserving injection `Fin n -> Fin (S n)` that skips
position `k`. When `lower j < lower k`, the result is
`weaken j` (same value); when `lower k ≤ lower j`, the
result is `fsuc j` (shifted up by one).

```agda

private
  skip : Fin (S n) -> Fin n -> Fin (S n)
  skip k j with cmp (lower k) (lower j)
  ... | inl _ = fsuc j
  ... | inr _ = weaken j

```

## Unskip map

Partial left inverse of `skip`. Given `k j : Fin (S n)`,
returns `inl i` when `j` misses `k` (with `skip k i ≡ j`),
or `inr true` when `j = k`. Three outcomes by two sequential
comparisons: hi (`j > k`, gives `fpred j`), hit (`j = k`,
gives `inr true`), lo (`j < k`, gives `unskip-restrict`).

```agda

private
  unskip-restrict
    : (kk : Fin (S n)) (jj : Fin (S n))
    -> lower jj < lower kk -> Fin n
  unskip-restrict
    (fin _ ⦃ bounded = forget kb ⦄)
    (fin j') j<k =
    fin j' ⦃ forget (lt-le-cat j<k kb) ⦄

  unskip
    : Fin (S n) -> Fin (S n) -> Fin n ⊎ Bool
  unskip kk jj with cmp (lower jj) (lower kk)
  ... | inr k<j = inl (fpred jj (lt.<→z< k<j))
  ... | inl j≤k with cmp (lower kk) (lower jj)
  ...   | inl k≤j = inr true
  ...   | inr j<k = inl (unskip-restrict kk jj j<k)

```

## Degeneracy maps

The degeneracy map `δ□ k` projects away dimension k. Each
coordinate j of the n-cube maps to the corresponding
coordinate of the (S n)-cube, skipping position k. This is
a pure variable map (no endpoints).

```agda

δ□ : Fin (S n) -> S n ⇒□ n
δ□ k j = inl (skip k j)

```

## Face maps

The face map `σ□ k e` inserts endpoint e at dimension k.
Each coordinate j of the (S n)-cube maps to either a
variable of the n-cube (when j misses k) or the constant
endpoint e (when j hits k).

```agda

σ□ : Fin (S n) -> Bool -> n ⇒□ S n
σ□ k e j with unskip k j
... | inl i = inl i
... | inr _ = inr e

```

## Cancellation identity

Inserting an endpoint at dimension k then projecting it away
gives the identity. The composition `σ□ k e ⨾□ δ□ k` unfolds
to `comp□ (δ□ k) (σ□ k e)`, which at each `j : Fin n` gives
`σ□ k e (skip k j)`.

The proof repeats the `with`-patterns that `skip` and `unskip`
use so both sides compute in lockstep. Each branch resolves by
`refl` or absurdity.

```agda

private
  unskip-fsuc
    : (kk : Fin (S n)) (jj : Fin n)
    -> lower kk ≤ lower jj
    -> unskip kk (fsuc jj) ≡ inl jj
  unskip-fsuc
    (fin k' ⦃ bounded = forget kb ⦄)
    (fin j' ⦃ bounded = forget jb ⦄) k≤j
    with cmp (S j') k'
  ... | inl Sj≤k =
    ex-falso
      (lt-le-absurd (lt.peel k' Sj≤k) k≤j)
  ... | inr k<Sj = ap inl (fin-path refl)

  unskip-weaken
    : (kk : Fin (S n)) (jj : Fin n)
    -> lower jj < lower kk
    -> unskip kk (weaken jj) ≡ inl jj
  unskip-weaken
    (fin k' ⦃ bounded = forget kb ⦄)
    (fin j' ⦃ bounded = forget jb ⦄) j<k
    with cmp j' k'
  ... | inr k<j =
    ex-falso (lt.irrefl (lt.cat j<k k<j))
  ... | inl j≤k with cmp k' j'
  ...   | inl k≤j =
    ex-falso (lt-le-absurd j<k k≤j)
  ...   | inr j<k' = ap inl (fin-path refl)

  cancel-pw
    : (kk : Fin (S n)) (e : Bool) (j : Fin n)
    -> (σ□ kk e ⨾□ δ□ kk) j ≡ id□ j
  cancel-pw
    kk@(fin k' ⦃ bounded = forget kb ⦄)
    e j@(fin j' ⦃ bounded = forget jb ⦄)
    with cmp k' j'
  ... | inl k≤j with cmp (S j') k'
  ...   | inl Sj≤k =
    ex-falso
      (lt-le-absurd (lt.peel k' Sj≤k) k≤j)
  ...   | inr k<Sj = ap inl (fin-path refl)
  cancel-pw
    kk@(fin k' ⦃ bounded = forget kb ⦄)
    e j@(fin j' ⦃ bounded = forget jb ⦄)
    | inr j<k with cmp j' k'
  ...   | inl j≤k with cmp k' j'
  ...     | inl k≤j =
    ex-falso (lt-le-absurd j<k k≤j)
  ...     | inr j<k' = ap inl (fin-path refl)
  cancel-pw
    kk@(fin k' ⦃ bounded = forget kb ⦄)
    e j@(fin j' ⦃ bounded = forget jb ⦄)
    | inr j<k | inr k<j =
    ex-falso (lt.irrefl (lt.cat j<k k<j))

δ□σ□-cancel
  : (kk : Fin (S n)) (e : Bool)
  -> σ□ kk e ⨾□ δ□ kk ≡ id□
δ□σ□-cancel kk e = funext (cancel-pw kk e)

```

## Skip helpers

Lemmas relating the `lower` value of `skip` results to the
comparison outcome. These parallel `σ-result-lo`/`σ-result-hi`
from `Core.Data.Fin.Monotone`.

```agda

private
  skip-lo-lower
    : (kk : Fin (S n)) (jj : Fin n)
    -> lower jj < lower kk
    -> lower (skip kk jj) ≡ lower jj
  skip-lo-lower kk jj lt
    with cmp (lower kk) (lower jj)
  ... | inl le = ex-falso (lt-le-absurd lt le)
  ... | inr _ = refl

  skip-hi-lower
    : (kk : Fin (S n)) (jj : Fin n)
    -> lower kk ≤ lower jj
    -> lower (skip kk jj) ≡ S (lower jj)
  skip-hi-lower kk jj le
    with cmp (lower kk) (lower jj)
  ... | inl _ = refl
  ... | inr lt = ex-falso (lt-le-absurd lt le)

```

## Degeneracy-degeneracy identity

Both sides are pure variable maps (`inl ∘ skip ∘ skip`), so the
proof reduces to showing skip compositions commute. The case
analysis parallels `σσ-comm` in `Core.Data.Fin.Monotone`.

```agda

  δ□δ□-pw
    : (i j : Fin (S n)) -> lower i ≤ lower j
    -> (k : Fin n)
    -> (δ□ (weaken i) ⨾□ δ□ j) k
     ≡ (δ□ (fsuc j) ⨾□ δ□ i) k
  -- LHS at k: inl (skip (weaken i) (skip j k))
  -- RHS at k: inl (skip (fsuc j) (skip i k))
  -- Case split on skip j k and skip i k via
  -- cmp on i'/j' vs k'
  δ□δ□-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄) i≤j
    k@(fin k' ⦃ bounded = forget kb ⦄)
    with cmp i' k' | cmp j' k'
  -- i ≤ k, j ≤ k: skip j k = fsuc k, skip i k = fsuc k
  --   LHS: skip (weaken i) (fsuc k), lower = S k'
  --     weaken i has lower i', i' ≤ k' < S k'
  --     so i' ≤ S k', giving hi: S (S k')
  --   RHS: skip (fsuc j) (fsuc k), lower = S k'
  --     fsuc j has lower S j', j' ≤ k' < S k'
  --     so S j' ≤ S k', giving hi: S (S k')
  ... | inl i≤k | inl j≤k = ap inl (fin-path
    ( skip-hi-lower (weaken i) (fsuc k) (step i≤k)
    ∙ sym (skip-hi-lower (fsuc j) (fsuc k)
        (lt.s<s j≤k))))
  -- i ≤ k, k < j: skip j k = weaken k, skip i k = fsuc k
  --   LHS: skip (weaken i) (weaken k), lower = k'
  --     weaken i has lower i', i' ≤ k'
  --     so hi: S k'
  --   RHS: skip (fsuc j) (fsuc k), lower = S k'
  --     fsuc j has lower S j', k' < j' so S k' < S j'
  --     meaning S k' < S j', so lo: S k'
  ... | inl i≤k | inr k<j = ap inl (fin-path
    ( skip-hi-lower (weaken i) (weaken k) i≤k
    ∙ sym (skip-lo-lower (fsuc j) (fsuc k)
        (lt.s<s k<j))))
  -- k < i, j ≤ k: impossible since i ≤ j
  ... | inr k<i | inl j≤k = ex-falso
    (lt-le-absurd
      (lt-le-cat j≤k (lt.s<s k<i)) i≤j)
  -- k < i, k < j: skip j k = weaken k, skip i k = weaken k
  --   LHS: skip (weaken i) (weaken k), lower = k'
  --     weaken i has lower i', k' < i'
  --     so lo: k'
  --   RHS: skip (fsuc j) (weaken k), lower = k'
  --     fsuc j has lower S j', k' < j' < S j'
  --     so lo: k'
  ... | inr k<i | inr k<j = ap inl (fin-path
    ( skip-lo-lower (weaken i) (weaken k) k<i
    ∙ sym (skip-lo-lower (fsuc j) (weaken k)
        (step k<j))))

δ□δ□-comm
  : (i j : Fin (S n)) -> lower i ≤ lower j
  -> δ□ (weaken i) ⨾□ δ□ j
   ≡ δ□ (fsuc j) ⨾□ δ□ i
δ□δ□-comm i j i≤j = funext (δ□δ□-pw i j i≤j)

```

## Unskip value lemmas

Direct lemmas about the result of `unskip` in each case. These
restate `unskip-fsuc` and `unskip-weaken` and add the "hit" case.

```agda

private
  -- When k' = lower kk, unskip hits: returns inr true
  unskip-self
    : (kk : Fin (S n))
    -> unskip kk kk ≡ inr true
  unskip-self (fin k' ⦃ bounded = forget kb ⦄)
    with cmp k' k'
  ... | inl k≤k with cmp k' k'
  ...   | inl _ = refl
  ...   | inr k<k = ex-falso (lt.irrefl k<k)
  unskip-self (fin k' ⦃ bounded = forget kb ⦄)
    | inr k<k = ex-falso (lt.irrefl k<k)

```

## Face map value lemmas

Direct lemmas about `σ□ kk ε` applied to specific arguments.

```agda

private
  -- σ□ kk ε (weaken jj) = inl jj when j < k
  σ□-lo
    : (kk : Fin (S n)) (jj : Fin n) (ε : Bool)
    -> lower jj < lower kk
    -> σ□ kk ε (weaken jj) ≡ inl jj
  σ□-lo
    (fin k' ⦃ bounded = forget kb ⦄)
    (fin j' ⦃ bounded = forget jb ⦄) ε j<k
    with cmp j' k'
  ... | inr k<j =
    ex-falso (lt.irrefl (lt.cat j<k k<j))
  ... | inl j≤k with cmp k' j'
  ...   | inl k≤j =
    ex-falso (lt-le-absurd j<k k≤j)
  ...   | inr j<k' = ap inl (fin-path refl)

  -- σ□ kk ε (fsuc jj) = inl jj when k ≤ j
  σ□-hi
    : (kk : Fin (S n)) (jj : Fin n) (ε : Bool)
    -> lower kk ≤ lower jj
    -> σ□ kk ε (fsuc jj) ≡ inl jj
  σ□-hi
    (fin k' ⦃ bounded = forget kb ⦄)
    (fin j' ⦃ bounded = forget jb ⦄) ε k≤j
    with cmp (S j') k'
  ... | inl Sj≤k =
    ex-falso
      (lt-le-absurd (lt.peel k' Sj≤k) k≤j)
  ... | inr k<Sj = ap inl (fin-path refl)

  -- σ□ kk ε kk = inr ε (hitting the face position)
  σ□-self
    : (kk : Fin (S n)) (ε : Bool)
    -> σ□ kk ε kk ≡ inr ε
  σ□-self (fin k' ⦃ bounded = forget kb ⦄) ε
    with cmp k' k'
  ... | inl k≤k with cmp k' k'
  ...   | inl _ = refl
  ...   | inr k<k = ex-falso (lt.irrefl k<k)
  σ□-self (fin k' ⦃ bounded = forget kb ⦄) ε
    | inr k<k = ex-falso (lt.irrefl k<k)

```

## Face-face identity (σ□σ□-comm)

Both sides have type `n ⇒□ S (S n)`. The pointwise proof
analyses five zones determined by where `k` sits relative to
`i` and `S j`, matching on the same comparisons that `unskip`
uses internally so that the `with`-abstraction forces the goal
to reduce.

```agda

private
  σ□σ□-pw
    : (i j : Fin (S n)) (ε ε' : Bool)
    -> lower i ≤ lower j
    -> (k : Fin (S (S n)))
    -> (σ□ i ε ⨾□ σ□ (fsuc j) ε') k
     ≡ (σ□ j ε' ⨾□ σ□ (weaken i) ε) k

  -- k = fin Z
  σ□σ□-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    ε ε' i≤j (fin Z ⦃ bounded = forget kb ⦄)
    with cmp Z (S j')
  ... | inr Sj<Z = ex-falso (lt.¬n<z Sj<Z)
  ... | inl Z≤Sj with cmp (S j') Z
  ...   | inl Sj≤Z =
    ex-falso (lt.¬n<z (lt.peel Z Sj≤Z))
  ...   | inr Z<Sj with cmp Z i'
  ...     | inr i<Z = ex-falso (lt.¬n<z i<Z)
  ...     | inl Z≤i with cmp i' Z
  ...       | inl i≤Z
    with cmp Z i'
  ...         | inr i<Z' =
    ex-falso (lt.¬n<z i<Z')
  ...         | inl Z≤i' with cmp i' Z
  ...           | inr Z<i =
    ex-falso (lt-le-absurd Z<i i≤Z)
  ...           | inl i≤Z' = refl
  σ□σ□-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    ε ε' i≤j (fin Z ⦃ bounded = forget kb ⦄)
    | inl Z≤Sj | inr Z<Sj | inl Z≤i | inr Z<i
    with cmp Z i'
  ...       | inr i<Z' =
    ex-falso (lt.¬n<z i<Z')
  ...       | inl Z≤i' with cmp i' Z
  ...         | inl i≤Z =
    ex-falso (lt-le-absurd Z<i i≤Z)
  ...         | inr Z<i' with cmp Z j'
  ...           | inr j<Z =
    ex-falso (lt.¬n<z j<Z)
  ...           | inl Z≤j with cmp j' Z
  ...             | inl j≤Z = ex-falso
    (lt-le-absurd
      (lt-le-cat Z<i i≤j) j≤Z)
  ...             | inr Z<j =
    ap inl (fin-path refl)

  -- k = fin (S k'')
  σ□σ□-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    ε ε' i≤j
    (fin (S k'') ⦃ bounded = forget kb ⦄)
    with cmp (S k'') (S j')
       | cmp (S k'') i'
  -- Both hi
  ... | inr Sj<Sk | inr i<Sk
    with k'' | cmp k'' i'
       | cmp k'' j'
  ... | Z | _ | _ =
    ex-falso (lt.¬n<z (lt.peel Z Sj<Sk))
  ... | S k''' | inl Sk≤i | _ =
    ex-falso (lt-le-absurd j<i i≤j) where
      j<i = lt-le-cat
        (lt.peel (S k''') Sj<Sk) Sk≤i
  ... | S k''' | inr i<Sk' | inl Sk≤j =
    ex-falso (lt-le-absurd
      (lt.peel (S k''') Sj<Sk) Sk≤j)
  ... | S k''' | inr i<Sk' | inr j<Sk' =
    ap inl (fin-path refl)
  -- Impossible: hi/lo
  σ□σ□-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    ε ε' i≤j
    (fin (S k'') ⦃ bounded = forget kb ⦄)
    | inr Sj<Sk | inl Sk≤i =
    ex-falso (lt-le-absurd j<i i≤j) where
      j<i = lt.peel _
        (lt.cat Sj<Sk Sk≤i)
  -- lo/hi: Zone 3 or 4
  σ□σ□-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    ε ε' i≤j
    (fin (S k'') ⦃ bounded = forget kb ⦄)
    | inl Sk≤Sj | inr i<Sk
    with cmp (S j') (S k'')
  -- Zone 4
  ...   | inl Sj≤Sk with cmp k'' j'
  ...     | inr j<k = ex-falso
    (lt-le-absurd (lt.s<s j<k) Sk≤Sj)
  ...     | inl k≤j with cmp j' k''
  ...       | inr k<j = ex-falso
    (lt-le-absurd (lt.s<s k<j) Sj≤Sk)
  ...       | inl j≤k = refl
  -- Zone 3
  σ□σ□-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    ε ε' i≤j
    (fin (S k'') ⦃ bounded = forget kb ⦄)
    | inl Sk≤Sj | inr i<Sk | inr Sk<Sj
    with cmp (S k'') i'
  ...   | inl Sk≤i =
    ex-falso (lt-le-absurd i<Sk Sk≤i)
  ...   | inr i<Sk' with cmp k'' j'
  ...     | inr j<k = ex-falso (lt.irrefl
    (lt.cat j<k (lt.peel j' Sk<Sj)))
  ...     | inl k≤j with cmp j' k''
  ...       | inl j≤k = ex-falso
    (lt-le-absurd (lt.peel j' Sk<Sj) j≤k)
  ...       | inr k<j = ap inl (fin-path refl)
  -- Both lo: Zone 1 or 2
  σ□σ□-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    ε ε' i≤j
    (fin (S k'') ⦃ bounded = forget kb ⦄)
    | inl Sk≤Sj | inl Sk≤i
    with cmp (S j') (S k'')
       | cmp i' (S k'')
  -- Absurd
  ...   | inl Sj≤Sk | _ = ex-falso
    (lt-le-absurd
      (lt.peel _ (le.cat Sj≤Sk Sk≤i))
      i≤j)
  -- Zone 2
  ...   | inr Sk<Sj | inl i≤Sk
    with cmp (S k'') i'
  ...     | inr i<Sk' =
    ex-falso (lt-le-absurd i<Sk' Sk≤i)
  ...     | inl Sk≤i' with cmp i' (S k'')
  ...       | inr Sk<i =
    ex-falso (lt-le-absurd Sk<i i≤Sk)
  ...       | inl i≤Sk' = refl
  -- Zone 1
  σ□σ□-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    ε ε' i≤j
    (fin (S k'') ⦃ bounded = forget kb ⦄)
    | inl Sk≤Sj | inl Sk≤i
    | inr Sk<Sj | inr Sk<i
    with cmp (S k'') i'
  ...     | inr i<Sk' = ex-falso
    (lt-le-absurd Sk<i (step i<Sk'))
  ...     | inl Sk≤i' with cmp i' (S k'')
  ...       | inl i≤Sk =
    ex-falso (lt-le-absurd Sk<i i≤Sk)
  ...       | inr Sk<i' with cmp (S k'') j'
  ...         | inr j<Sk = ex-falso
    (lt-le-absurd
      (lt.peel j' Sk<Sj) j<Sk)
  ...         | inl Sk≤j with cmp j' (S k'')
  ...           | inl j≤Sk = ex-falso
    (lt-le-absurd
      (lt-le-cat Sk<i i≤j) j≤Sk)
  ...           | inr Sk<j =
    ap inl (fin-path refl)

σ□σ□-comm
  : (i j : Fin (S n)) (ε ε' : Bool)
  -> lower i ≤ lower j
  -> σ□ i ε ⨾□ σ□ (fsuc j) ε'
   ≡ σ□ j ε' ⨾□ σ□ (weaken i) ε
σ□σ□-comm i j ε ε' i≤j =
  funext (σ□σ□-pw i j ε ε' i≤j)

```

## Degeneracy-face interchange (lt case)

When `lower i < lower j`, the degeneracy and face maps
interchange as `σ□ (fsuc j) e ⨾□ δ□ (weaken i) ≡ δ□ i ⨾□ σ□ j e`.

The proof matches on the RHS's `unskip j k` sequentially
(first `cmp k' j'`, then `cmp j' k'` only
in the `inl` branch), producing three zones. Within each
zone the LHS comparisons are matched to force reduction.

```agda

private
  δ□σ□-lt-pw
    : (i j : Fin (S n)) (e : Bool)
    -> lower i < lower j
    -> (k : Fin (S n))
    -> (σ□ (fsuc j) e ⨾□ δ□ (weaken i)) k
     ≡ (δ□ i ⨾□ σ□ j e) k

  -- RHS unskip step 1: cmp k' j'
  δ□σ□-lt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e i<j
    k@(fin k' ⦃ bounded = forget kb ⦄)
    with cmp k' j'
  -- Step 1 inl: k' ≤ j'. Now step 2: cmp j' k'.
  ... | inl k≤j with cmp j' k'
  -- Hit zone: k ≈ j. RHS = inr e.
  -- LHS skip (weaken i) k: cmp i' k'.
  ...   | inl j≤k with cmp i' k'
  --   i ≤ k: fsuc k. unskip (S j') (S k'):
  --     step 1: cmp (S k') (S j')
  ...     | inl i≤k with cmp (S k') (S j')
  ...       | inr Sj<Sk =
    ex-falso
      (lt-le-absurd
        (lt.peel k' Sj<Sk) k≤j)
  --       step 1 inl: step 2: cmp (S j') (S k')
  ...       | inl Sk≤Sj with cmp (S j') (S k')
  ...         | inr Sk<Sj =
    ex-falso
      (lt-le-absurd
        (lt.peel j' Sk<Sj) j≤k)
  ...         | inl _ = refl
  -- Hit zone, k < i: absurd since k ≈ j and i < j
  δ□σ□-lt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e i<j
    k@(fin k' ⦃ bounded = forget kb ⦄)
    | inl k≤j | inl j≤k | inr k<i =
    ex-falso
      (lt-le-absurd
        (lt.cat k<i i<j) j≤k)
  -- Lo zone: k < j. RHS = inl (skip i (unskip-restrict ...)).
  -- Both sides use cmp i' k'. Match it.
  δ□σ□-lt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e i<j
    k@(fin k' ⦃ bounded = forget kb ⦄)
    | inl k≤j | inr k<j with cmp i' k'
  -- i ≤ k: both give fsuc. unskip (S j') (S k'):
  --   step 1: cmp (S k') (S j')
  ...   | inl i≤k with cmp (S k') (S j')
  ...     | inr Sj<Sk =
    ex-falso
      (lt.irrefl
        (lt.cat k<j (lt.peel k' Sj<Sk)))
  --     step 1 inl: step 2: cmp (S j') (S k')
  ...     | inl Sk≤Sj with cmp (S j') (S k')
  ...       | inl Sj≤Sk =
    ex-falso
      (lt-le-absurd (lt.s<s k<j) Sj≤Sk)
  ...       | inr _ = ap inl (fin-path refl)
  -- k < i: weaken on both. unskip (S j') (k' ...):
  --   step 1: cmp k' (S j')
  δ□σ□-lt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e i<j
    k@(fin k' ⦃ bounded = forget kb ⦄)
    | inl k≤j | inr k<j | inr k<i
    with cmp k' (S j')
  ...   | inr Sj<k =
    ex-falso
      (lt-le-absurd (step k<j) (step Sj<k))
  --   step 1 inl: step 2: cmp (S j') k'
  ...   | inl k≤Sj with cmp (S j') k'
  ...     | inl Sj≤k =
    ex-falso
      (lt-le-absurd (step k<j) Sj≤k)
  ...     | inr _ = ap inl (fin-path refl)
  -- Hi zone: j' < k' (step 1 inr). fpred k.
  -- k = Z absurd.
  δ□σ□-lt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e i<j
    (fin Z ⦃ bounded = forget kb ⦄)
    | inr j<Z = ex-falso (lt.¬n<z j<Z)
  -- k = S k'': fpred k has lower k''.
  -- Match skip i (fpred k): cmp i' k''
  -- and skip (weaken i) k: cmp i' (S k'').
  δ□σ□-lt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e i<j
    (fin (S k'') ⦃ bounded = forget kb ⦄)
    | inr j<Sk
    with cmp i' k''
       | cmp i' (S k'')
  -- i ≤ k'' and i ≤ S k'': fsuc on both.
  --   unskip (S j') (S (S k'')): cmp (S (S k'')) (S j')
  ...   | inl _ | inl _
    with cmp (S (S k'')) (S j')
  ...     | inl SSk≤Sj =
    ex-falso
      (lt-le-absurd j<Sk
        (lt.peel (S j') SSk≤Sj))
  ...     | inr _ = ap inl (fin-path refl)
  -- i ≤ k'' but S k'' < i: absurd
  δ□σ□-lt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e i<j
    (fin (S k'') ⦃ bounded = forget kb ⦄)
    | inr j<Sk
    | inl i≤k'' | inr Sk<i =
    ex-falso (lt-le-absurd Sk<i (step i≤k''))
  -- k'' < i and i ≤ S k'': absurd
  δ□σ□-lt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e i<j
    (fin (S k'') ⦃ bounded = forget kb ⦄)
    | inr j<Sk
    | inr k''<i | inl _ =
    ex-falso
      (lt-le-absurd
        (lt-le-cat (lt.s<s k''<i) (lt.s<s i<j))
        (step j<Sk))
  -- k'' < i and S k'' < i: weaken on both.
  --   unskip (S j') (S k''): cmp (S k'') (S j')
  δ□σ□-lt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e i<j
    (fin (S k'') ⦃ bounded = forget kb ⦄)
    | inr j<Sk
    | inr k''<i | inr Sk<i
    with cmp (S k'') (S j')
  ...   | inl _ =
    ex-falso
      (lt.irrefl
        (lt-le-cat (lt.cat k''<i i<j) j<Sk))
  ...   | inr _ = ap inl (fin-path refl)

δ□σ□-interchange-lt
  : (i j : Fin (S n)) (e : Bool)
  -> lower i < lower j
  -> σ□ (fsuc j) e ⨾□ δ□ (weaken i)
   ≡ δ□ i ⨾□ σ□ j e
δ□σ□-interchange-lt i j e i<j =
  funext (δ□σ□-lt-pw i j e i<j)

```

## Degeneracy-face interchange (gt case)

When `lower j < lower i`, the degeneracy and face maps
interchange as `σ□ (weaken j) e ⨾□ δ□ (fsuc i) ≡ δ□ i ⨾□ σ□ j e`.

The proof follows the same sequential strategy as the lt
case but with `σ□ (weaken j)` and `δ□ (fsuc i)`.

```agda

private
  δ□σ□-gt-pw
    : (i j : Fin (S n)) (e : Bool)
    -> lower j < lower i
    -> (k : Fin (S n))
    -> (σ□ (weaken j) e ⨾□ δ□ (fsuc i)) k
     ≡ (δ□ i ⨾□ σ□ j e) k

  -- RHS unskip step 1: cmp k' j'
  δ□σ□-gt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e j<i
    k@(fin k' ⦃ bounded = forget kb ⦄)
    with cmp k' j'
  -- Step 1 inl: k' ≤ j'. Now step 2: cmp j' k'.
  ... | inl k≤j with cmp j' k'
  -- Hit zone: k ≈ j. RHS = inr e.
  -- LHS skip (fsuc i) k: cmp (S i') k'.
  ...   | inl j≤k with cmp (S i') k'
  --   S i' ≤ k': absurd since k ≈ j < i
  ...     | inl Si≤k =
    ex-falso
      (lt-le-absurd j<i
        (lt.cat (lt.peel k' Si≤k) k≤j))
  --   k' < S i': weaken k. unskip (fin j') (fin k' ...):
  --     step 1: cmp k' j'
  ...     | inr k<Si with cmp k' j'
  ...       | inr j<k' =
    ex-falso (lt-le-absurd j<k' k≤j)
  --       step 1 inl: step 2: cmp j' k'
  ...       | inl _ with cmp j' k'
  ...         | inr k<j' =
    ex-falso (lt-le-absurd k<j' j≤k)
  ...         | inl _ = refl
  -- Lo zone: k < j. RHS = inl (skip i (unskip-restrict ...)).
  -- Match skip i: cmp i' k'
  -- and skip (fsuc i) k: cmp (S i') k'.
  δ□σ□-gt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e j<i
    k@(fin k' ⦃ bounded = forget kb ⦄)
    | inl k≤j | inr k<j
    with cmp i' k'
       | cmp (S i') k'
  -- i ≤ k and S i' ≤ k': absurd since k < j < i
  ...   | inl _ | inl Si≤k =
    ex-falso
      (lt.irrefl
        (lt.cat (lt.peel k' Si≤k)
          (lt.cat k<j j<i)))
  -- i ≤ k and k < S i': absurd since k < j < i ≤ k
  ...   | inl i≤k | inr _
    with cmp k' j'
  ...     | inr j<k' =
    ex-falso (lt-le-absurd j<k' k≤j)
  ...     | inl _ with cmp j' k'
  ...       | inl j≤k =
    ex-falso (lt-le-absurd k<j j≤k)
  ...       | inr _ =
    ex-falso
      (lt-le-absurd
        (lt.cat k<j j<i) i≤k)
  -- k < i and S i' ≤ k': absurd
  δ□σ□-gt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e j<i
    k@(fin k' ⦃ bounded = forget kb ⦄)
    | inl k≤j | inr k<j
    | inr k<i | inl Si≤k =
    ex-falso
      (lt.irrefl
        (lt.cat (lt.peel k' Si≤k) k<i))
  -- k < i and k < S i': both give weaken, lower k'.
  --   unskip (fin j') (fin k' ...):
  --     step 1: cmp k' j'
  δ□σ□-gt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e j<i
    k@(fin k' ⦃ bounded = forget kb ⦄)
    | inl k≤j | inr k<j
    | inr k<i | inr _
    with cmp k' j'
  ...   | inr j<k' =
    ex-falso (lt-le-absurd j<k' k≤j)
  --   step 1 inl: step 2: cmp j' k'
  ...   | inl _ with cmp j' k'
  ...     | inl j≤k =
    ex-falso (lt-le-absurd k<j j≤k)
  ...     | inr _ = ap inl (fin-path refl)
  -- Hi zone: j' < k' (step 1 inr). fpred k.
  -- k = Z absurd.
  δ□σ□-gt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e j<i
    (fin Z ⦃ bounded = forget kb ⦄)
    | inr j<Z = ex-falso (lt.¬n<z j<Z)
  -- k = S k'': fpred k has lower k''.
  -- Match skip i (fpred k): cmp i' k''
  -- and skip (fsuc i) k: cmp (S i') (S k'').
  δ□σ□-gt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e j<i
    k@(fin (S k'') ⦃ bounded = forget kb ⦄)
    | inr j<Sk
    with cmp i' k''
       | cmp (S i') (S k'')
  -- i ≤ k'' and S i' ≤ S k'': fsuc on both.
  --   unskip (fin j') (fin (S (S k''))):
  --     step 1: cmp (S (S k'')) j'
  ...   | inl _ | inl _
    with cmp (S (S k'')) j'
  ...     | inl SSk≤j =
    ex-falso
      (lt.irrefl
        (lt.cat j<Sk (lt.peel j' SSk≤j)))
  ...     | inr _ = ap inl (fin-path refl)
  -- i ≤ k'' but S k'' < S i': absurd
  δ□σ□-gt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e j<i
    k@(fin (S k'') ⦃ bounded = forget kb ⦄)
    | inr j<Sk
    | inl i≤k'' | inr Sk<Si =
    ex-falso (lt-le-absurd Sk<Si (lt.s<s i≤k''))
  -- k'' < i and S i' ≤ S k'': absurd
  δ□σ□-gt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e j<i
    k@(fin (S k'') ⦃ bounded = forget kb ⦄)
    | inr j<Sk
    | inr k''<i | inl Si≤Sk =
    ex-falso
      (lt-le-absurd k''<i
        (lt.peel (S k'') Si≤Sk))
  -- k'' < i and S k'' < S i': weaken on both.
  --   unskip (fin j') (fin (S k'')):
  --     step 1: cmp (S k'') j'
  δ□σ□-gt-pw
    i@(fin i' ⦃ bounded = forget ib ⦄)
    j@(fin j' ⦃ bounded = forget jb ⦄)
    e j<i
    k@(fin (S k'') ⦃ bounded = forget kb ⦄)
    | inr j<Sk
    | inr k''<i | inr Sk<Si
    with cmp (S k'') j'
  ...   | inl Sk≤j =
    ex-falso
      (lt-le-absurd j<Sk Sk≤j)
  ...   | inr _ = ap inl (fin-path refl)

δ□σ□-interchange-gt
  : (i j : Fin (S n)) (e : Bool)
  -> lower j < lower i
  -> σ□ (weaken j) e ⨾□ δ□ (fsuc i)
   ≡ δ□ i ⨾□ σ□ j e
δ□σ□-interchange-gt i j e j<i =
  funext (δ□σ□-gt-pw i j e j<i)

```
