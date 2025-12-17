```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}


open import Lib.Graph.Reflexive.Base
module Lib.Graph.Reflexive.Polynomial {u v} (R : Rx u v)where

open import Lib.Core.Prim
open import Lib.Core.Type
open import Lib.Core.Base
open import Lib.Path
open import Lib.Graph.Reflexive.Lens.Covariant R
open import Lib.Graph.Reflexive.Lens.Contravariant R
open Rx R renaming (₀ to Ob; ₁ to infix 4 _~>_)

-- Covariant partial product P⁺
-- Given: S with vertex extraction F : S.₀ → Ob, and target T
-- Result: pairs (s, f) where f : F s → T.₀
module cov-poly {w z w' z'} (S : Rx w z) (T : Rx w' z') where
  private
    module S = Rx S
    module T = Rx T

  module _ (F : S.₀ → Ob) (F-edge : ∀ {s t} → S.₁ s t → F s ~> F t) where

    -- P⁺ : Rx (w ⊔ u ⊔ w') (z ⊔ v ⊔ z')
    -- P⁺ .Rx.₀ = Σ s ∶ S.₀ , (F s → T.₀)
    -- P⁺ .Rx.₁ (s , f) (t , g) =
    --   Σ e ∶ S.₁ s t , (∀ i → T.₁ (f i) (g (subst (λ x → x) {!!} i)))
    -- P⁺ .Rx.ρ (s , f) = S.ρ s , λ i → T.ρ (f i)

-- Contravariant partial product P⁻
-- module ctrv-poly {w z w' z'} (S : Rx w z) (T : Rx w' z') where
--   private
--     module S = Rx S
--     module T = Rx T

--   module _ (F : S.₀ → Ob) (F-edge : ∀ {s t} → S.₁ s t → F s ~> F t) where

--     P⁻ : Rx (w ⊔ u ⊔ w') (z ⊔ v ⊔ z')
--     P⁻ .Rx.₀ = Σ s ∶ S.₀ , (F s → T.₀)
--     P⁻ .Rx.₁ (s , f) (t , g) =
--       Σ e ∶ S.₁ s t , (∀ i → T.₁ (f {!!}) (g i))
--     P⁻ .Rx.ρ (s , f) = S.ρ s , λ i → T.ρ (f i)
