```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.List.Disjoint where

open import Lib.Type
open import Lib.Sigma
open import Data.List
open import Lib.Cubical.Base
open import Lib.Path.Erased

open import Rel.Ternary.Base
open import Rel.Ternary.SepAlg

pattern _:<_ x xs = xs ∷ x
infixl 8 _:<_

data Disj {u} {A : Type u} : [ A ] → [ A ] → [ A ] → Type u where
  done : Disj [] [] []
  inl : ∀ {as bs cs} → Disj as bs cs → ∀ {k} → Disj (as :< k) bs (cs :< k)
  inr : ∀ {as bs cs} → Disj as bs cs → ∀ {k} → Disj as (bs :< k) (cs :< k)

module _ {u} {A : Type u} where
  Disj→Path : {as bs : [ A ]} → Disj [] as bs → as ≡ bs
  Disj→Path done = λ _ → []
  Disj→Path (inr p {k}) = λ i → Disj→Path p i :< k

  Disj-idl : (as : [ A ]) → Disj [] as as
  Disj-idl [] = done
  Disj-idl (as :< x) = inr (Disj-idl as)

  Disj-comm : {as bs cs : [ A ]} → Disj as bs cs → Disj bs as cs
  Disj-comm done = done
  Disj-comm (inl p) = inr (Disj-comm p)
  Disj-comm (inr p) = inl (Disj-comm p)

  Disj-assoc : {a b c ab abc : [ A ]} → Disj a b ab → Disj ab c abc
             → Σ bc :: List A , (Disj a bc abc × Disj b c bc)
  Disj-assoc done done = [] , done , done
  Disj-assoc done (inr q {k}) =
    let (bc , d1 , d2) = Disj-assoc done q
    in (bc :< k) , inr d1 , inr d2
  Disj-assoc (inl p) (inl q) =
    let (bc , d1 , d2) = Disj-assoc p q
    in bc , inl d1 , d2
  Disj-assoc (inl p {k}) (inr q) =
    let (bc , d1 , d2) = Disj-assoc (inl p) q
    in bc :< _ , inr d1 , inr d2
  Disj-assoc (inr p) (inl q) =
    let (bc , d1 , d2) = Disj-assoc p q
    in (bc :< _) , inr d1 , inl d2
  Disj-assoc (inr p) (inr q) =
    let (bc , d1 , d2) = Disj-assoc (inr p) q
    in _ , inr d1 , inr d2

Disj-SepAlg : ∀ {u} (A : Type u) → has-separation-alg (record { _<>_<>_ = Disj {A = A} })
Disj-SepAlg A .has-separation-alg.unit = []
Disj-SepAlg A .has-separation-alg.idl = Disj-idl
Disj-SepAlg A .has-separation-alg.to-path = Disj→Path
Disj-SepAlg A .has-separation-alg.comm = Disj-comm
Disj-SepAlg A .has-separation-alg.assoc = Disj-assoc
