Order-preserving maps between finite types -- simplicial identities.

Re-exports simplicial identity proofs from Base. These proofs live in
Base because they require with-abstraction visibility into σ-map and
δ-map internals.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Fin.Monotone.Properties where

open import Core.Data.Fin.Monotone.Base public
  using ( δσ-cancel-weaken
        ; δσ-cancel-fsuc
        ; δδ-comm
        ; σσ-comm
        ; δσ-interchange-lt
        ; δσ-interchange-gt
        )

```
