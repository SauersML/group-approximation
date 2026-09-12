import GroupApproximation.CharClass.OddPSign
-- for `singFreeR`, whose differential IS the slot boundary; see `tagBd`
import GroupApproximation.CharClass.OddPSingular
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CupProduct
-- `faceSimplex` is declared in `AlexanderWhitneyFaceMaps.lean` l.247, which
-- `CupProduct.lean` does NOT import (it imports `AlexanderWhitney.lean`).  The
-- error is "Unknown identifier", which reads as a missing `open` and is a
-- missing module.
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.AlexanderWhitneyFaceMaps
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
-- `Finset.Iio` on `Fin r` needs `Fin.instLocallyFiniteOrder`
-- (`Mathlib/Order/Interval/Finset/Fin.lean` l.33 at pin `81a5d257`).
import Mathlib.Order.Interval.Finset.Fin

/-!
# The `r`-fold tensor power of the singular chains, flat and signed

The target of both acyclic-models comparisons in this lane.  The arity `r` is a
**free parameter**, so `C(X)^{⊗p}` and the Cartan target `C(X)^{⊗2p}` are the
same object at two values of `r` and share every lemma; that is the whole reason
for building it by hand rather than iterating a binary tensor.

## Why not the alternatives

* **Mathlib's iterated `tensorCx`.**  The cyclic permutation of `r` factors needs
  a braiding, and at pin `81a5d257` `Mathlib/Algebra/Homology/Monoidal.lean`
  provides `MonoidalCategory` for `HomologicalComplex` but no braided or
  symmetric instance; the graded-object braiding is not transported to
  complexes.  Building a `p`-cycle out of associators for a *variable* `p` is not
  affordable.
* **A signed port of `CartanFreeCx`.**  It is binary, so the cyclic shift is a
  composite of `r - 1` adjacent transpositions with `r` variable, and every
  degree becomes an expression in the inputs — the failure mode
  `CartanMidFour`'s post-mortem is about.

## Design

Three recipes from the mod-2 lanes, all load-bearing here.

* **Degrees as data, the constraint as a `Prop`.**  `TupIdx` carries the whole
  tuple of tagged simplices and the sum condition as a subtype; this is
  cc-steenrod's `PairIdx`/`PairDeg` shape, which is what removed every degree
  cast from their lane.
* **`abbrev`, not `def`.**  `rw` checks type-correctness at `instances`
  transparency and will not unfold a plain `def`, so a semireducible index type
  makes every goal mentioning a component untouchable.  Six failures in one probe
  bought that rule.
* **Totalise.**  `tupUpdate` returns `0` unless the updated tuple lands in the
  target total degree, so no sum carries a side condition and no index appears
  with a proof argument.  `tagBd` likewise returns `0` on a `0`-simplex, by a
  `Nat` eliminator whose *result type does not mention the degree*, which is what
  lets `congrArg` cross it with no dependent motive.

This file defines the carrier, the boundary of a single tagged simplex, and the
differential.  The cyclic action, `d ∘ d = 0` and acyclicity are later files.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
-- `faceSimplex` lives one namespace deeper, in `…SphereOddDegree.AlexanderWhitney`
-- (`AlexanderWhitneyFaceMaps.lean` l.247); opening only `SphereOddDegree` leaves
-- it unknown, and the follow-on error is a misleading "function expected".
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

/-! ## 1. The index type -/

/-- A singular simplex carrying its own degree.  A plain `Sigma`, so that a
tuple of them is a plain function and pushing one forward is not a dependent
rewrite. -/
abbrev TagSimp (X : TopCat.{0}) : Type := Σ n : ℕ, singularSimplices X n

/-- The degree-`k` index of the `r`-fold tensor power: `r` tagged simplices whose
degrees sum to `k`. -/
abbrev TupIdx (X : TopCat.{0}) (r k : ℕ) : Type :=
  { t : Fin r → TagSimp X // ∑ j, (t j).1 = k }

/-- The degree-`k` carrier: the free `K`-module on `TupIdx`. -/
abbrev tupMod (K : Type) [CommRing K] (X : TopCat.{0}) (r k : ℕ) : Type :=
  TupIdx X r k →₀ K

/-- The Koszul prefix: the total degree of the slots strictly before `j`.  The
sign of an operator applied in slot `j` is `(-1)` to this power.

Stated on a bare tuple rather than on a `TupIdx` on purpose: the contraction of
the acyclicity argument has to evaluate it on its **input** while its output's
prefix slots have collapsed to degree `0`, and a version that could only be
applied to the value would silently compute the wrong sign there. -/
def tupPre {X : TopCat.{0}} {r : ℕ} (t : Fin r → TagSimp X) (j : Fin r) : ℕ :=
  ∑ l ∈ Finset.Iio j, (t l).1

/-! ## 2. The boundary of one tagged simplex -/

/-- Tag every simplex of a chain with the degree `n`. -/
noncomputable def tagAt (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) :
    (singularSimplices X n →₀ K) →ₗ[K] (TagSimp X →₀ K) :=
  Finsupp.lmapDomain K K (fun σ => (⟨n, σ⟩ : TagSimp X))

@[simp] theorem tagAt_single (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X n) :
    tagAt K X n (Finsupp.single σ (1 : K))
      = Finsupp.single (⟨n, σ⟩ : TagSimp X) (1 : K) := by
  rw [tagAt]
  show Finsupp.lmapDomain K K _ _ = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- **The boundary of a single tagged simplex: the differential of `singFreeR`,
retagged.**  `0` in degree `0`.

Defined categorically rather than as an explicit alternating face sum, and that
is the whole design.  The two facts the tuple differential ever uses of this map
are that it lowers the degree by exactly one and that it squares to zero, and
both are now true **by construction** — the second from
`HomologicalComplex.d_comp_d`.  An explicit sum would have to be identified with
the differential afterwards, which is `OddPTupleBd.lean`, parked and red; and
proving square-zero from the simplicial identity instead is not an option,
because that identity is not in the vendored layer under any spelling.

Nothing is lost by hiding the face signs: the mixed-term cancellation that
carries the odd-primary content never inspects them, since whatever happens
inside a slot happens identically in both orders of differentiation.

The `Nat` eliminator is on the degree and the **result type does not mention
it**, so this still crosses `congrArg` with no dependent motive. -/
noncomputable def tagBd (K : Type) [CommRing K] (X : TopCat.{0}) :
    TagSimp X → (TagSimp X →₀ K)
  | ⟨0, _⟩ => 0
  | ⟨n + 1, σ⟩ =>
      tagAt K X n ((((singFreeR K).obj X).d (n + 1) n).hom (Finsupp.single σ (1 : K)))

@[simp] theorem tagBd_zero (K : Type) [CommRing K] (X : TopCat.{0})
    (σ : singularSimplices X 0) : tagBd K X ⟨0, σ⟩ = 0 := rfl

@[simp] theorem tagBd_succ (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X (n + 1)) :
    tagBd K X ⟨n + 1, σ⟩
      = tagAt K X n ((((singFreeR K).obj X).d (n + 1) n).hom
          (Finsupp.single σ (1 : K))) := rfl

/-- The explicit alternating face sum, kept as a *consequence* rather than as the
definition, for whoever needs the signs. -/
theorem tagBd_succ_eq_sum (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X (n + 1)) :
    tagBd K X ⟨n + 1, σ⟩
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          Finsupp.single (⟨n, faceSimplex X n i σ⟩ : TagSimp X) (1 : K) := by
  rw [tagBd_succ, singFreeR_d_single, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, tagAt_single]

/-! ## 3. The differential -/

/-- Replace slot `j` of a tuple by a tagged simplex, as an element of the
degree-`k` carrier: the corresponding basis element when the degrees then sum to
`k`, and `0` otherwise.

Totalised deliberately.  The alternative — a partial function with the degree
equation as a hypothesis — puts a proof argument inside a definition, which
blocks every later rewrite. -/
noncomputable def tupUpdate (K : Type) [CommRing K] {X : TopCat.{0}} {r : ℕ} (k : ℕ)
    (t : Fin r → TagSimp X) (j : Fin r) (τ : TagSimp X) : tupMod K X r k :=
  if h : ∑ l, (Function.update t j τ l).1 = k then
    Finsupp.single (⟨Function.update t j τ, h⟩ : TupIdx X r k) (1 : K)
  else 0

theorem tupUpdate_of_ne (K : Type) [CommRing K] {X : TopCat.{0}} {r k : ℕ}
    (t : Fin r → TagSimp X) (j : Fin r) (τ : TagSimp X)
    (h : ¬ (∑ l, (Function.update t j τ l).1 = k)) :
    tupUpdate K k t j τ = 0 := dif_neg h

/-- The differential on one basis element: differentiate each slot in turn, with
the Koszul prefix sign of that slot. -/
noncomputable def tupDGen (K : Type) [CommRing K] (X : TopCat.{0}) (r k : ℕ)
    (t : TupIdx X r (k + 1)) : tupMod K X r k :=
  ∑ j : Fin r,
    ((-1 : K) ^ tupPre t.1 j) •
      Finsupp.linearCombination K (fun τ : TagSimp X => tupUpdate K k t.1 j τ)
        (tagBd K X (t.1 j))

/-- **The differential of the `r`-fold tensor power.** -/
noncomputable def tupD (K : Type) [CommRing K] (X : TopCat.{0}) (r k : ℕ) :
    tupMod K X r (k + 1) →ₗ[K] tupMod K X r k :=
  Finsupp.linearCombination K (fun t : TupIdx X r (k + 1) => tupDGen K X r k t)

@[simp] theorem tupD_single (K : Type) [CommRing K] (X : TopCat.{0}) (r k : ℕ)
    (t : TupIdx X r (k + 1)) :
    tupD K X r k (Finsupp.single t (1 : K)) = tupDGen K X r k t := by
  rw [tupD, Finsupp.linearCombination_single, one_smul]

end GroupApproximation.CharClass
