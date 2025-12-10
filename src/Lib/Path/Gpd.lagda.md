Lane Biocini
October 23, 2025

Some debt is owed to the fantastic erased cubical development related to
"Compiling Programs with Erased Univalence" by Nils Anders Danielsson,
located (here)[https://www.cse.chalmers.se/~nad/listings/dependent-lenses/README.Compiling-Programs-with-Erased-Univalence.html].

Where I built upon this was my realization that we could build an unbiased
composition operator in cubical by computing a path between a left-biased
and right-biased composition operator, and then defining our canonical
composite as a diagonal over a path `composite p q : catl p q ≡ catr p q`,
where we can then define `cat p q i = composite p q (~ i) i : A`,
which ends up yielding great behavior for consistent and principled
derivation of all the Groupoid laws - all groupoid lemmas systematically
use our conn lemma generating squares of the form `Square p p q q`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Lib.Path.Gpd where

open import Lib.Type
open import Lib.Builtin
open import Lib.Equal hiding (refl)
open import Lib.Cubical.Base
open import Lib.Cubical.Kan hiding (fill)
open import Lib.Path

private variable
  u v : Level
  A : I → Type u

module cat2 {u} {A : I → Type u} where
  sys : {w x : A i0} {y z : A i1}
      → x ≡ w → x ≡ y :: A → y ≡ z
      → (i : I) → Partials (∂ i) (λ _ → A i)
  sys p q r i = λ where
    j (i = i0) → p j
    j (j = i0) → q i
    j (i = i1) → r j

  cat2 : {w x : A i0} {y z : A i1}
      → x ≡ w → x ≡ y :: A → y ≡ z → w ≡ z :: A
  cat2 p q r i = hcomp (∂ i) (sys p q r i)

  fill : {w x : A i0} {y z : A i1}
       → (p : x ≡ w) (q : x ≡ y :: A) (r : y ≡ z)
       → SquareP (λ i _ → A i) p q r (cat2 p q r)
  fill p q r i j = hfill (∂ i) j (sys p q r i)

  refl : {x : A i0} {y : A i1} (p : x ≡ y :: A) → cat2 rfl p rfl ≡ p
  refl p i j = fill rfl p rfl j (~ i)

  is-composite : {w : A i0} {z : A i1} → w ≡ z :: A → A i0 → A i1 → Type u
  is-composite {w} {z} s x y = Σ p :: (x ≡ w)
                             , Σ q :: (x ≡ y :: A)
                             , Σ r :: (y ≡ z)
                             , Square p q r s

  record Path-composite {x : A i0} {z : A i1} (s : x ≡ z :: A) : Type u where
    field
      {a0} : A i0
      {a1} : A i1
      composite : is-composite s a0 a1

open cat2 using (cat2; Path-composite; is-composite) public
{-# DISPLAY hcomp _ (cat2.sys p q r i) = cat2 p q r i #-}

module catr {x : A i0} {y : A i1} where
  sys : {z : A i1} (p : x ≡ y :: A) (q : y ≡ z)
      → (i : I) → Partials (∂ i) (iconst (A i))
  sys p q i k (i = i0) = x
  sys p q i k (k = i0) = p i
  sys p q i k (i = i1) = q k

  catr : {z : A i1} → x ≡ y :: A → y ≡ z → x ≡ z :: A
  catr p q = cat2 rfl p q

  fill : {z : A i1} (p : x ≡ y :: A) (q : y ≡ z)
       → rfl ≡ q :: ∂.square _≡_ p (catr p q)
  fill p q = cat2.fill rfl p q

  refl : (p : x ≡ y :: A) → catr p rfl ≡ p
  refl p i j = fill p rfl j (~ i)

open catr using (catr) public
{-# DISPLAY hcomp _ (catr.sys p q j) = catr p q j #-}
{-# DISPLAY hfill _ _ (catr.sys p q i j) = catr.fill p q i j #-}

module catl {y : A i0} {z : A i1} where
  catl : {x : A i0} → x ≡ y → y ≡ z :: A → x ≡ z :: A
  catl p q = cat2 (hsym p) q rfl

  fill : {x : A i0} (p : x ≡ y) (q : y ≡ z :: A)
       → hsym p ≡ rfl :: ∂.square _≡_ q (catl p q)
  fill p q = cat2.fill (hsym p) q rfl

  refl : (q : y ≡ z :: A) → catl rfl q ≡ q
  refl q j i = fill rfl q i (~ j)

open catl using (catl) public

hconn : {A : I → Type u} {x y : A i0} {z : A i1}
     → (p : x ≡ y) (q : y ≡ z :: A)
     → SquareP (λ i j → A (i ∧ j)) p p q q
hconn {A} {y} {z} p q i j = hcomp (∂ i ∨ ∂ j) sys
  module hconn where
    sys : Partials (∂ i ∨ ∂ j) (λ _ → A (i ∧ j))
    sys k (k = i0) = q (i ∧ j)
    sys k (i = i0) = p (j ∨ ~ k)
    sys k (j = i0) = p (i ∨ ~ k)
    sys k (j = i1) = q i
    sys k (i = i1) = q j
{-# DISPLAY hcomp _ (hconn.sys p q i j) = hconn p q i j #-}

conn : {A : Type u} {x y z : A} (p : x ≡ y) (q : y ≡ z) → Square p p q q
conn = hconn

module cat where
  module _ {A : I → Type u} {x : A i0} {y z : A i1} (p : x ≡ y :: A) (q : y ≡ z) where
    sys : (i : I) → Partials (∂ i) (λ _ → A i)
    sys i k (i = i0) = x
    sys i k (k = i0) = p i
    sys i k (i = i1) = q k

    cat : x ≡ z :: A
    cat i = hcomp (∂ i) (sys i)

    fill : rfl ≡ q :: ∂.square _≡_ p cat
    fill i j = hfill (∂ i) j (sys i)

  private
    infixr 40 _∙_
    _∙_ = cat

  module _ {A : I → Type u} where
    cfill : {x : A i0} {y z : A i1} (p : x ≡ y :: A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ ~ j)) (hsym p) rfl q (p ∙ q)
    cfill {y} p q i j = hcomp (∂ i ∨ ~ j) λ where
      k (j = i0) → y
      k (i = i0) → p (~ j)
      k (k = i0) → p (i ∨ ~ j)
      k (i = i1) → q (j ∧ k)

    bfill : {x : A i0} {y z : A i1} (p : x ≡ y :: A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ j)) p (p ∙ q) rfl q
          -- p ≡ rfl :: ∂.square _≡_ (p ∙ q) q
    bfill p q i j = hcomp (∂ i ∨ j) λ where
      k (i = i0) → p j
      k (i = i1) → q k
      k (j = i1) → q (i ∧ k)
      k (k = i0) → p (i ∨ j)

    rfill : {x : A i0} {y z : A i1} (p : x ≡ y :: A) (q : y ≡ z)
          → SquareP (λ i j → A (i ∨ ~ j)) (hsym p) q rfl (p ∙ q)
          -- → hsym p ≡ erfl z :: ∂.square _≡_ q (p ∙ q)
    rfill {y} p q i j = hcomp (∂ i ∨ ~ j) λ where
      k (j = i0) → q (i ∧ k)
      k (i = i0) → p (~ j)
      k (k = i0) → p (i ∨ ~ j)
      k (i = i1) → q k

  cone : {A : Type u} {x y z : A} (q : y ≡ z) (r : x ≡ z)
       → Square q (cat q (hsym r)) r (erfl z)
  cone q r i j = hcomp (∂ i ∨ j) λ where
    k (i = i0) → q (j ∧ k)
    k (i = i1) → r (j ∨ ~ k)
    k (j = i1) → q (i ∨ k)
    k (k = i0) → q i

  fan : {A : Type u} {x y z : A} (p : x ≡ y) (q : x ≡ z)
      → Square p (erfl x) q (cat (hsym p) q)
  fan {x} p q i j = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → p j
    k (j = i0) → x
    k (i = i1) → q (j ∧ k)
    k (k = i0) → p (~ i ∧ j)

  lpush : {A : Type u} {w x y z : A}
        → (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
        → Square p q r s → Square (erfl x) q r (p ∙ s)
  lpush {x} p q r s sq i j = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → x
    k (j = i0) → q (i ∧ k)
    k (i = i1) → sq k j
    k (k = i0) → p (i ∧ j)

  rpush : {A : Type u} {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
        → Square p q r s → Square p (erfl x) (q ∙ r) s
  rpush {x} p q r s sq i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → x
    k (i = i0) → p (j ∧ k)
    k (j = i1) → sq i k
    k (k = i0) → q (i ∧ j)

  rpop : {A : Type u} {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
       → Square p (erfl x) (q ∙ r) s → Square p q r s
  rpop p q r s sq i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p j
    k (i = i1) → bfill q r j k 
    k (j = i0) → q (i ∧ k)
    k (j = i1) → s i
    k (k = i0) → sq i j

  -- compositor : {A : I → Type u} {w x : A i0} {y z : A i1}
  --            → (p : w ≡ x) (q : x ≡ y :: A) (r : y ≡ z)
  --            → Square {!!} (cat q r) {!!} (cat2 {!!} q r)
  -- compositor p q r i j = hcomp (∂ i ∨ ~ j) λ where
  --   k (i = i0) → {!!} -- p (~ k)
  --   k (i = i1) → {!!} -- fill q r j k
  --   k (j = i0) → {!!} -- p (i ∨ ~ k)
  --   k (k = i0) → {!!} -- q (i ∧ j)

  unique : {A : I → Type u} {x : A i0} {y z : A i1}
         → {p : x ≡ y :: A} {q : y ≡ z} (r : x ≡ z :: A)
         → Square (erfl x) p q r
         → r ≡ p ∙ q
  unique {p} {q} r sq i =
    Composite.unique rfl p q (r , sq) (p ∙ q , fill p q) i .fst

  Tri : {A : I → Type u} {x : A i0} {y z : A i1}
      → x ≡ y :: A → y ≡ z → x ≡ z :: A → Type u
  Tri p q s = s ≡ p ∙ q

  unitl : {A : Type u} {x y : A} (p : x ≡ y) → rfl ∙ p ≡ p
  unitl p i j = rfill rfl p j (~ i)

  unitr : {x : A i0} {y : A i1} (p : x ≡ y :: A) → p ∙ rfl ≡ p
  unitr p i j = fill p rfl j (~ i)

  invl : {A : Type u} {x y : A} (p : x ≡ y) → cat (hsym p) p ≡ rfl
  invl {x} {y} p i j = hcomp (∂ j ∨ i) λ where
        k (j = i0) → y
        k (k = i0) → p (~ j)
        k (j = i1) → p k
        k (i = i1) → p (~ j ∨ k)

  invr : {A : Type u} {x y : A} (p : x ≡ y) → cat p (hsym p) ≡ rfl
  invr p = invl (hsym p)

  assoc : {A : Type u} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
        → cat p (cat q r) ≡ cat (cat p q) r
  assoc {y} p q r k = transpose (fill p q) k ∙ transpose (rfill q r) (~ k)

  hsqueeze : {A : Type u} {x y : A} {p q : x ≡ y} → p ∙ rfl ≡ rfl ∙ q → p ≡ q
  hsqueeze {p} {q} h = cat2 (unitr p) h (unitl q)

  vsqueeze : {A : Type u} {x y : A} {p q : x ≡ y} → rfl ∙ p ≡ q ∙ rfl → p ≡ q
  vsqueeze {p} {q} h = cat2 (unitl p) h (unitr q)

  baxter : {A : Type u} {w x y z : A}
         → (p : w ≡ x) (q : w ≡ y) (r : y ≡ z) (s : x ≡ z) (c : x ≡ y)
         → (H : Square p rfl q c)
         → (K : Square s c r rfl)
         → p ∙ s ≡ q ∙ r
  baxter {w} {x} {y} {z} p q r s c H K i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → w -- H i (~ k)
    k (i = i0) → fill p s j k -- fill p s j k
    k (j = i1) → K i k -- s (i ∨ k)
    k (k = i0) → H i j -- K i j

  commutes : {A : Type u} {w x y z : A}
           → (p : w ≡ x) (q : x ≡ z) (r : w ≡ y) (s : y ≡ z)
           → Square p r s q → cat p q ≡ cat r s
  commutes {w} p q r s sq i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → p (~ i ∧ ~ k)
    k (j = i1) → s (~ i ∨ k)
    k (i = i0) → rfill p q j k
    k (k = i0) → sq j (~ i)

  lwhisker : {A : Type u} {x y z : A} (p : x ≡ y) {q r : y ≡ z} → q ≡ r → p ∙ q ≡ p ∙ r
  lwhisker p = ap (cat p)

  rwhisker : {A : Type u} {x y z : A} {p q : x ≡ y} (r : y ≡ z) → p ≡ q → p ∙ r ≡ q ∙ r
  rwhisker r = ap (_∙ r)

open cat using (cat) public

{-# DISPLAY hcomp _ (cat.sys p q i) = cat p q i #-}

-- cat : {A : I → Type u} {x y : A i0} {z : A i1} (p : x ≡ y) (q : y ≡ z :: A) → x ≡ z :: A
-- cat p q = cat2 (hsym p) q rfl

ap-sq : {A : Type u} {B : Type v} (f : A → B) {x00 x10 x01 x11 : A}
      → {p : x00 ≡ x01} {q : x00 ≡ x10} {r : x10 ≡ x11} {s : x01 ≡ x11}
      → Square p q r s
      → Square (ap f p) (ap f q) (ap f r) (ap f s)
ap-sq f sq i j = f (sq i j)

sq-cancel : {A : Type u} {x y z : A} (p : x ≡ y) (q : y ≡ z) → Square q (hsym p) p (hsym q)
sq-cancel p q i j = conn p q (~ i) j

tri-vinv : {A : Type u} {x y z : A} (p : x ≡ z) (q : x ≡ y) (r : y ≡ z)
         → Square p q r rfl → Square p rfl q (hsym r)
tri-vinv p q r sq i j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → p j
  k (i = i1) → sq-cancel q r k j
  k (j = i0) → q (i ∧ ~ k)
  k (j = i1) → r (~ i ∨ ~ k)
  k (k = i0) → sq i j

paste : {A : Type u} {w x y z : A}
      → {p : w ≡ x} (w0 : x ≡ z)
      → {q : w ≡ y} (w1 : y ≡ z)
      → (r : x ≡ y)
      → Square w0 r w1 (erfl z)
      → Square (hsym p) rfl r q
      → Square p q w1 w0
paste {w} {x} {z} {p} w0 {q} w1 r sq1 sq2 i j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i1) → sq1 k j
  k (j = i0) → sq2 i k
  k (j = i1) → sq1 (~ k) i
  k (k = i0) → tri-vinv w0 r w1 sq1 (~ i) (j)
  k (i = i0) → conn p r j (~ k)

paste-alt : {A : Type u} {w x y z : A}
      → (p : w ≡ x) (q : w ≡ y) (r : x ≡ y)
      → (w0 : x ≡ z) (w1 : y ≡ z)
      → Square w0 r w1 rfl
      → Square p (erfl w) q r
      → Square q p w0 w1
paste-alt p q r w0 w1 sq sq2 i j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i1) → tri-vinv w0 r w1 sq (~ k) (j)
  k (j = i0) → p i
  k (j = i1) → conn q w1 i k
  k (k = i0) → sq2 j i
  k (i = i0) → q (j ∧ k)

loop-rfl : {A : Type u} {x y : A} (p : x ≡ y) (q : y ≡ y)
         → Square p rfl p q → q ≡ rfl
loop-rfl p q sq i j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → conn p q j k
  k (i = i1) → p (j ∨ k)
  k (j = i0) → p k
  k (j = i1) → q (i ∨ k)
  k (k = i0) → sq i j

module contr-map {v} {A : Type u} {B : Type v} {f : A → B} (e : is-qinv f) where
  private
    g = e .is-qinv.inv
    η = e .is-qinv.sec
    ε = e .is-qinv.retr

  module _ {y : B} ((x , p) : fiber f y) where
    faces0 : (i j : I) → Partial (∂ i ∨ ~ j) A
    faces0 i = λ where
      k (i = i0) → g y
      k (i = i1) → η (g y) k
      k (k = i0) → g (ε y (~ i))

    faces1 : (i j : I) → Partial (∂ i ∨ ~ j) A
    faces1 i = λ where
      k (i = i0) → g y
      k (i = i1) → η x k
      k (k = i0) → g (p (~ i))

    private
      π₀ : g y ≡ g y
      π₀ i = hcomp (∂ i) (faces0 i)

      θ₀ : Square rfl (ap g (hsym (ε y))) (η (g y)) π₀
      θ₀ i j = hfill (∂ i) j (faces0 i)

      π₁ : g y ≡ x
      π₁ i = hcomp (∂ i) (faces1 i)

      θ₁ : Square rfl (ap g (hsym p)) (η x)  π₁
      θ₁ i j = hfill (∂ i) j (faces1 i)

      fiber-sys : (i j : I) → Partial (∂ i ∨ ~ j) A
      fiber-sys i = λ where
        j (i = i0) → π₀ j
        j (i = i1) → π₁ j
        j (j = i0) → g y

      path : g y ≡ x
      path i = hcomp (∂ i) (fiber-sys i)

      fiber-filler : Square π₀ rfl π₁ path
      fiber-filler i j = hfill (∂ i) j (fiber-sys i)

      ι : Square (ap g (ε y)) (ap (λ z → g (f z)) path) (ap g p) rfl
      ι i j = hcomp (∂ i ∨ ∂ j) λ where
        k (i = i0) → θ₀ (~ j) (~ k)
        k (i = i1) → θ₁ (~ j) (~ k)
        k (j = i0) → η (path i) (~ k)
        k (j = i1) → g y
        k (k = i0) → fiber-filler i (~ j)

      filler : Square (ε y) (ap f path) p rfl
      filler i j = hcomp (∂ i ∨ ∂ j) λ where
        k (i = i0) → ε (ε y j) k
        k (i = i1) → ε (p j) k
        k (j = i0) → ε (f (path i)) k
        k (j = i1) → ε y k
        k (k = i0) → f (ι i j)

    unit : g (f x) ≡ x
    unit i = hcomp (∂ i) λ where
      j (i = i0) → g (f x)
      j (i = i1) → path j
      j (j = i0) → g (p i)

    counit : f (g y) ≡ y
    counit = ε y

    private
      φ : Square rfl p (hsym (ε y)) (ap f (hsym path))
      φ = tri.by-comp (hsym (ε y)) (ap f path) (hsym p) (rrotate filler)

    adj : ap f unit ≡ ε (f x)
    adj i j = hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → f (cat2.fill rfl (ap g p) path j k)
      k (i = i1) → ε (p (~ k)) j
      k (j = i0) → f (g (p (i ∧ ~ k)))
      k (j = i1) → φ (~ k) (~ i)
      k (k = i0) → conn (ap (λ z → (f (g z))) p) (ε y) i j

    fiber-path : Path (fiber f y) (g y , ε y) (x , p)
    fiber-path i .fst = path i
    fiber-path i .snd = filler i

  contr : (y : B) → is-contr (fiber f y)
  contr y .ctr = g y , ε y
  contr y .paths = fiber-path

-- fiber-paths : ∀ {v} {A : Type u} {B : Type v} {f : A → B} {y : B}
--             → {f1 f2 : fiber f y}
--             → f1 ≡ f2
--             → Σ p :: f1 .fst ≡ f2 .fst , ap f p ∙ f2 .snd ≡ f1 .snd
-- fiber-paths {f} p = {!!} where
--   c = contr-map.fiber-path (record { inv = {!!} ; sec = {!!} ; retr = {!!} })

-- homotopy-natural : ∀ {u v} {A : Type u} {B : Type v}
--                → {f g : A → B}
--                → (H : (x : A) → f x ≡ g x)
--                → {x y : A} (p : x ≡ y)
--                → H x ∙ ap g p ≡ ap f p ∙ H y
-- homotopy-natural {f = f} {g = g} H {x} {y} p =
  -- commutes2 (H x) (ap g p) (ap f p) (H y) λ i j →
  --   hcomp (∂ j ∨ ~ i) λ where
  --     k (j = i0) → H (p i) (~ k)
  --     k (j = i1) → {!H (p i) (k ∧ i)!}
  --     k (i = i0) → H x (~ k ∧ ~ i)
  --     k (k = i0) → {!H (p i) (i)!}

  -- cat-unique _ λ i j →
  -- hcomp (∂ j ∨ ∂ i) λ where
  --   k (i = i0) → H x (j ∧ ~ k) -- H (p k) j -- H (p k) j
  --   k (i = i1) → {!!}  -- f (p (i ∧ k)) -- f (p (i ∧ k))
  --   k (j = i0) → {!!} -- H x (i ∧ j) -- H x (i ∧ j)
  --   k (j = i1) → {!!} -- H x (i ∧ j) -- H x (i ∧ j)
  --   k (k = i0) → H x j -- H x (i ∧ j) -- H x (i ∧ j)

```
module cat where
  private
    _∙_ = cat

  infixr 40 _∙_
  module _ {A : I → Type u} {x y : A i0} {z : A i1} (p : x ≡ y) (q : y ≡ z :: A) where
    fill : SquareP (λ i j → A (i ∧ j)) (hsym p) rfl q (cat p q)
    fill i j = hcomp (∂ i ∨ ~ j) λ where
      k (i = i0) → p (~ j ∨ ~ k)
      k (j = i0) → y
      k (i = i1) → q j
      k (k = i0) → q (i ∧ j)

    lfill : SquareP (λ i j → A (i ∧ j)) rfl p q (cat p q)
    lfill i j = hcomp (∂ i ∨ ~ j) λ where
      k (i = i0) → p (~ k)
      k (i = i1) → q j
      k (j = i0) → p (i ∨ ~ k)
      k (k = i0) → q (i ∧ j)

    cfill : Square p (cat p q) rfl q
    cfill i j = hcomp (∂ i ∨ j) λ where
      k (i = i0) → p (j ∨ ~ k)
      k (j = i1) → q i
      k (i = i1) → z
      k (k = i0) → q i

  cone : {A : Type u} {x y z : A} (q : y ≡ z) (r : x ≡ z)
   → Square q (cat q (hsym r)) r rfl
  cone {z = z} q r i j = hcomp (∂ i ∨ j) λ where
    k (i = i0) → q (j ∨ ~ k)
    k (k = i0) → r (~ i ∨ j)
    k (i = i1) → r j
    k (j = i1) → z

  fan : {A : Type u} {x y z : A} (p : x ≡ y) (q : x ≡ z)
   → Square p rfl q (cat (hsym p) q)
  fan p q = fill (hsym p) q

  rfill : {A : Type u} {x y z : A} (p : x ≡ y) (q : y ≡ z)
        → Square (hsym p) q rfl (cat p q)
  rfill p q i j = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → p (~ j ∨ ~ k)
    k (i = i1) → q (j ∨ k)
    k (j = i0) → q (i ∧ k)
    k (k = i0) → q (i ∧ j)

  compositor-coh : {A : Type u} {w x y z : A}
                 → (p : x ≡ w) (q : x ≡ y) (r : y ≡ z)
                 → Square p rfl (cat q r) (cat2 p q r)
  compositor-coh p q r i j = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → p (j ∧ k)
    k (i = i1) → fill q r j k
    k (j = i0) → q (~ k ∧ i)
    k (k = i0) → q i

  injl : {A : I → Type u} {x y : A i0} {z : A i1}
       → (p : x ≡ y) {q r : y ≡ z :: A}
       → cat p q ≡ cat p r → q ≡ r
  injl {z} p {q} {r} h i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → cfill p q j k
    k (i = i1) → cfill p r j k
    k (j = i0) → p k
    k (j = i1) → z
    k (k = i0) → h i j

  -- injr : {A : I → Type u} {x y : A i0} {z : A i1}
  --      → {p q : x ≡ y} (r : y ≡ z :: A) → cat p r ≡ cat q r → p ≡ q
  -- injr {A} {x} {y} {z} {p} {q} r h i j = hcomp (∂ i ∨ ∂ j) λ where
  --   k (i = i0) → {!!}
  --   k (i = i1) → {!!}
  --   k (j = i0) → {!!}
  --   k (j = i1) → {!transport-filler (λ k → A (~ k)) ? i1 !}
  --   k (k = i0) → coei0 A j (h i j)

  unique : {A : Type u} {x y z : A}
                 → {p : x ≡ y} {q : y ≡ z} (r : x ≡ z)
                 → Square rfl p q r
                 → r ≡ p ∙ q
  unique {p} {q} r sq i =
    Path-filler.unique rfl p q (r , sq) (p ∙ q , lfill p q) i .fst

  compositor : {A : Type u} {w x y z : A}
             → (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
             → Square p q r s
             → s ≡ cat2 p q r
  compositor p q r s sq i =
    Path-filler.unique p q r (s , sq) ((cat2 p q r) , cat2.fill p q r) i .fst

  Tri : {A : I → Type u} {x y : A i0} {z : A i1} (p : x ≡ y) (q : y ≡ z :: A) (s : x ≡ z :: A) → Type u
  Tri p q s = s ≡ p ∙ q

  invl : {A : Type u} {x y : A} (p : x ≡ y) → cat (hsym p) p ≡ rfl
  invl {x} {y} p i j = hcomp (∂ j ∨ i) sys
    module invl where
      sys = λ where
        k (j = i0) → p (i ∨ k)
        k (k = i0) → p (i ∨ j)
        k (j = i1) → y
        k (i = i1) → y

  {-# DISPLAY hcomp _ (invl.sys p q i) = invl p q i #-}

  invr : {A : Type u} {x y : A} (p : x ≡ y) → cat p (hsym p) ≡ rfl
  invr p = invl (hsym p)

  unitl : {A : Type u} {x y : A} (p : x ≡ y) → cat rfl p ≡ p
  unitl {x} {y} p i j = hcomp (∂ j ∨ i) sys
    module unitl where
      sys = λ where
        k (j = i0) → x
        k (k = i0) → p j
        k (j = i1) → y
        k (i = i1) → p j

  {-# DISPLAY hcomp _ (unitl.sys p q i) = unitl p q i #-}

  unitr : {A : Type u} {x y : A} (p : x ≡ y) → cat p rfl ≡ p
  unitr {x} {y} p i j = hcomp (∂ j ∨ i) sys
    module unitr where
      sys = λ where
        k (j = i0) → p (~ k)
        k (k = i0) → y
        k (j = i1) → y
        k (i = i1) → p (j ∨ ~ k)
  {-# DISPLAY hcomp _ (unitr.sys p q i) = unitr p q i #-}

  assoc : {A : Type u} {w x y z : A} → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
        → cat p (cat q r) ≡ cat (cat p q) r
  assoc {y} p q r i j = hcomp (∂ j ∨ ~ i) sys where
    sys = λ where
      k (j = i0) → cfill p q (~ k) (~ k)
      k (j = i1) → r (i ∨ k)
      k (k = i0) → r (i ∧ j)
      k (i = i0) → hcomp (∂ j ∨ ~ k) λ where
        i (j = i0) → cfill p q (~ k) (~ i)
        i (j = i1) → r (~ i ∨ k)
        i (k = i0) → r (~ i ∧ j)
        i (i = i0) → cfill q r j (~ k)

  hsqueeze : {A : Type u} {x y : A} {p q : x ≡ y} → p ∙ rfl ≡ rfl ∙ q → p ≡ q
  hsqueeze {p} {q} h = cat2 (unitr p) h (unitl q)

  vsqueeze : {A : Type u} {x y : A} {p q : x ≡ y} → rfl ∙ p ≡ q ∙ rfl → p ≡ q
  vsqueeze {p} {q} h = cat2 (unitl p) h (unitr q)

  lpush : {A : Type u} {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
         → Square p q r s → Square rfl q r (cat p s)
  lpush p q r s sq i j = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → p (~ k ∧ j)
    k (j = i0) → q i
    k (i = i1) → r j
    k (k = i0) → sq i j

  rpush : {A : Type u} {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
         → Square p q r s → Square p rfl (cat q r) s
  rpush p q r s sq i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → q (i ∧ ~ k)
    k (i = i0) → p j
    k (j = i1) → s i
    k (k = i0) → sq i j

  lpop : {A : Type u} {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
       → Square p rfl (cat q r) s → Square p q r s
  lpop p q r s sq i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p j
    k (i = i1) → cfill q r j k
    k (j = i0) → q (i ∧ k)
    k (j = i1) → s i
    k (k = i0) → sq i j

  commutes : {A : Type u} {x y z : A}
        → {p p' : x ≡ y} {q q' : y ≡ z}
        → Square p p' q' q → cat p q  ≡ cat p' q'
  commutes {p} {p'} {q} {q'} sq i j = hcomp (∂ j ∨ i) λ where
    k (j = i0) → p (~ i ∧ ~ k)
    k (j = i1) → q' (~ i ∨ k)
    k (i = i1) → lfill p' q' j k
    k (k = i0) → sq j (~ i)

  commutes' : {A : Type u} {w x y z : A}
        → {p p' : w ≡ x} {q q' : x ≡ y} {r r' : y ≡ z}
        → Square p (cat p' q') r' (cat q r) → cat p (cat q r) ≡ cat p' (cat q' r')
  commutes' {p} {p'} {q} {q'} {r} {r'} sq i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → p' (~ k ∧ i)  
    k (j = i1) → assoc p' q' r' i j
    k (i = i0) → cat p (cat q r) j
    k (k = i0) → hcomp (∂ j ∨ ~ i) λ where
      k (i = i0) → cat p (cat q r) (j ∧ k)
      k (j = i1) → cat p (cat q r) (i ∨ k)
      k (k = i0) → rpush (cat p' q') p (cat q r) r' (λ i j → sq j i) j i
      k (j = i0) → lfill p' q' i (~ k)

  commutes2 : {A : Type u} {w x y z : A}
            → (p : w ≡ x) (q : x ≡ z) (r : w ≡ y) (s : y ≡ z)
            → Square p r s q → cat p q ≡ cat r s
  commutes2 p q r s sq i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → r (i ∧ ~ k)
    k (j = i1) → q (i ∨ k)
    k (i = i0) → lfill p q j k
    k (k = i0) → sq i j

  rpop : {A : Type u} {w x y z : A} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z) (s : w ≡ z)
         → Square rfl p s (cat q r) → Square p q r s
  rpop p q r s sq i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p j
    k (i = i1) → cfill q r j k
    k (j = i0) → q (i ∧ k)
    k (j = i1) → s i
    k (k = i0) → sq j i

  coh : {A : Type u} {x y z : A} (p : x ≡ y) (q : y ≡ z) → cat p q ≡ cat2 (hsym p) rfl q
  coh {y} p q i j = hcomp (∂ j ∨ ~ i) λ where
    k (j = i0) → p (~ k)
    k (j = i1) → q k
    k (i = i0) → fill p q j k
    k (k = i0) → y

module Braid (F : Type u → Type u) (A : Type u) (c : A → F A → F A) where
  Brd : Type u
  Brd = (x y : A) (xs : F A) → c x (c y xs) ≡ c y (c x xs)

  Yank : Brd → Type u
  Yank t = (x : A) (xs : F A) → t x x xs ≡ rfl

catd : {A : Type u} (B : A → Type v) {x y z : A}
     → {a : B x} {b : B y} {c : B z}
     → {p : x ≡ y} {q : y ≡ z}
     → a ≡ b :: ∂.line B p
     → b ≡ c :: ∂.line B q
     → a ≡ c :: ∂.line B (cat p q)
catd B {c} {p} {q} u v i =
  comp (∂.line B (cat.rfill p q i)) (∂ i) sys where
    sys : Partials (∂ i) (∂.line B (cat.rfill p q i))
    sys k (i = i0) = u (~ k)
    sys k (i = i1) = c
    sys k (k = i0) = v i
```
-- module Reasoning where
--   -- From: https://www.cse.chalmers.se/~nad/publications/danielsson-erased-html/Equality.Path.html#5422
--   infix  -1 finally finally-h
--   infixr -2 step-≡ step-≡h step-≡hh _≡⟨⟩_

--   step-≡ : ∀ x {y z} → y ≡ z :: A → x ≡ y → x ≡ z :: A
--   step-≡ _ p q = cat q p

--   syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

--   step-≡h : ∀ x {y z} → y ≡ z → x ≡ y :: A → x ≡ z :: A
--   step-≡h _ p q = catr q p

--   syntax step-≡h x y≡z x≡y = x ≡⟨ x≡y ⟩op y≡z

--   step-≡hh : {A : Type u} {x y z : A} {x≡y : x ≡ y} {y≡z : y ≡ z}
--            → (P : A → Type u) (p : P x) {q : P y} {r : P z}
--            → q ≡ r :: (λ i → P (y≡z i))
--            → p ≡ q :: (λ i → P (x≡y i))
--            → p ≡ r :: (λ i → P (cat x≡y y≡z i))
--   step-≡hh P _ p q = hcat P q p

--   syntax step-≡hh P p q≡r p≡q = p ≡⟨ p≡q ⟩[ P ] q≡r

--   _≡⟨⟩_ : ∀ x {y} → x ≡ y :: A → x ≡ y :: A
--   _ ≡⟨⟩ x≡y = x≡y

--   finally : {A : Type u} (x y : A) → x ≡ y → x ≡ y
--   finally _ _ x≡y = x≡y

--   syntax finally x y x≡y = x ≡⟨ x≡y ⟩∎ y ∎

--   finally-h : ∀ x y → x ≡ y :: A → x ≡ y :: A
--   finally-h _ _ x≡y = x≡y

--   syntax finally-h x y x≡y = x ≡⟨ x≡y ⟩∎h y ∎
```
module Coh where
  composite : {A : Type u} {x y z : A} (p : x ≡ y) (q : y ≡ z) → catl p q ≡ catr p q
  composite p q i j = hcomp (∂ j) sys
    module composite where
      sys = λ where
        k (j = i0) → p (~ i ∧ ~ k)
        k (k = i0) → sq-cancel p q i j
        k (j = i1) → q (~ i ∨ k)

  cmp : {A : Type u} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  cmp p q i = composite p q (~ i) i

  module _ {A : Type u}  where
    coh : {x y z : A} (p : x ≡ y) (q : y ≡ z)
        → SquareP (∂.cube _≡_ q (catl p q) p (catr p q) (sq-cancel p q) (composite p q))
            (catl.fill p q) (lhs (hsym p)) (catr.fill p q) (hsym (lhs q))
    coh p q i j k = hcomp (∂ j ∨ ~ k) λ where
      l (j = i0) → p (~ i ∧ ~ k ∨ ~ l)
      l (k = i0) → conn p q (~ i) j
      l (l = i0) → conn p q (~ i) j
      l (j = i1) → q (~ i ∨ k ∧ l)

    cat-cat : {x y z : A} (p : x ≡ y) (q : y ≡ z) → cat p q ≡ cmp p q
    cat-cat p q j = λ k → coh p q (~ k) k j

    fill : {x y z : A} (p : x ≡ y) (q : y ≡ z)
         → Square (hsym p) rfl q (cmp p q)
    fill p q i j = hcomp (∂ i ∨ ~ j) sys where
      sys = λ where
        k (i = i0) → p (~ j)
        k (k = i0) → conn p q i (i ∨ ~ j)
        k (j = i0) → q (i ∧ ~ k)
        k (i = i1) → q (j ∨ ~ k)

    lfill : {x y z : A} (p : x ≡ y) (q : y ≡ z)
          → Square rfl p q (cmp p q)
    lfill p q i j = hcomp (∂ i ∨ ~ j) λ where
      k (i = i0) → p (~ j ∧ ~ k)
      k (i = i1) → q (j ∧ i)
      k (j = i0) → p (i ∨ ~ k)
      k (k = i0) → cat.fill p q i j

    rfill : {x y z : A} (p : x ≡ y) (q : y ≡ z)
          → Square (hsym p) q rfl (cmp p q)
    rfill p q i j = hcomp (∂ i ∨ ~ j) λ where
      k (i = i0) → p (~ j ∧ k)
      k (k = i0) → conn p q i (i ∧ j)
      k (j = i0) → conn p q i k
      k (i = i1) → q (j ∨ k)

    sfill : {x y z : A} (p : x ≡ y) (q : y ≡ z)
          → Square p rfl (cmp p q) q
    sfill p q i j = hcomp (∂ j ∨ ~ i) λ where
      k (j = i0) → p (~ i ∧ ~ k)
      k (i = i0) → p (j ∨ ~ k)
      k (j = i1) → q i
      k (k = i0) → cat.fill p q j i

    idpt : (x : A) → cmp rfl rfl ≡ erfl x
    idpt x i j = fill (erfl x) rfl j (~ i)

  module _ {A : Type u} {x y : A} where
    invl : (p : x ≡ y) → cmp (hsym p) p ≡ rfl
    invl p i j = hcomp (∂ j ∨ i) sys where
      sys = λ where
        k (j = i0) → p (~ i ∨ k)
        k (k = i0) → conn (hsym p) p j (i ∨ j)
        k (j = i1) → y
        k (i = i1) → p (j ∨ k)

    invr : (p : x ≡ y) → cmp p (hsym p) ≡ rfl
    invr p i j = hcomp (∂ j ∨ i) sys where
      sys = λ where
        k (j = i0) → p (i ∧ ~ k)
        k (k = i0) → conn p (hsym p) j (i ∨ j)
        k (j = i1) → x
        k (i = i1) → p (~ j ∧ ~ k)

    unitl : (p : x ≡ y) → cmp rfl p ≡ p
    unitl p i j = hcomp (∂ j ∨ i) sys where
      sys = λ where
        k (j = i0) → x
        k (k = i0) → conn rfl p j (i ∨ j)
        k (j = i1) → y
        k (i = i1) → p j

    unitr : (p : x ≡ y) → cmp p rfl ≡ p
    unitr p i j = hcomp (∂ j ∨ i) sys where
      sys = λ where
        k (j = i0) → p (i ∧ ~ k)
        k (k = i0) → conn p rfl j (i ∨ j)
        k (j = i1) → y
        k (i = i1) → p (j ∨ ~ k)

  assoc : {A : Type u} {w x y z : A} → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
        → cmp p (cmp q r) ≡ cmp (cmp p q) r
  assoc {y} p q r i j = hcomp (∂ j ∨ i) sys where
    sys = λ where
      k (j = i0) → cmp p q (i ∧ ~ k)
      k (j = i1) → r (~ i ∨ k)
      k (i = i1) → fill (cmp p q) r j k
      k (k = i0) → hcomp (∂ i ∨ j) λ where
        k (i = i0) → conn p (cmp q r) j (j ∧ k)
        k (i = i1) → y
        k (j = i1) → fill q r k (~ i)
        k (k = i0) → conn p q i (i ∨ j)
```
