Lane Biocini
Jun 30, 2024

Combinators for reasoning. Notice that we can define composition,
identity, and reasoning chains with the same record.

```
{-# OPTIONS --safe #-}

module Lib.Trait.Cut where

open import Lib.Prim

module _ {u v w} where
 record Cut (X : u type)
            (A : X → v type)
            (B : ∀ x → A x → w type) : uω where
  infixl 40 seq _∙_
  infixr 40 _∘_
  infixr 2 cut-syntax

  field
   seq : ∀ {x} (a : A x) → B x a
  {-# INLINE seq #-}

  _∙_ : ∀ {x} (a : A x) → B x a
  _∙_ = seq
  {-# INLINE _∙_ #-}

  syntax cut-syntax x a b = x ⟩ a ≡ b
  _∘_ cut-syntax : ∀ x → (a : A x) → B x a

  _∘_ x = seq {x}
  cut-syntax x = seq {x}
  {-# INLINE _∘_ #-}
  {-# INLINE cut-syntax #-}

 open Cut ⦃ ... ⦄ public

{-# DISPLAY Cut.seq _ = _∙_ #-}
{-# DISPLAY Cut._∙_ _ = _∙_ #-}
{-# DISPLAY Cut._∘_ _ = _∘_ #-}
