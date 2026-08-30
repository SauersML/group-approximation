import GroupApproximation.GGT.ElementaryClosure
import GroupApproximation.GGT.HullSCConeOffHeavyGeomSep

/-!
# From a conjugate common power to geometric separation

`GGT/HullSCConeOffHeavyGeomSep.lean` states `IsGeometricallySeparated` and
model-tests it.  What B2 owes is that the elementary closures of a family of
pairwise non-commensurable loxodromic elements satisfy it — the content Hull
takes from the proof of Dahmani--Guirardel--Osin's Theorem 6.8.

That proof has two halves, and they are of quite different kinds.  The
**geometric** half turns the diameter hypothesis into long oriented
fellow-travelling of two translated quasi-axes and then applies their Lemma 6.7
to get a conjugate common power.  The **algebraic** half turns that common power
into the two conclusions geometric separation asks for.  This module proves the
algebraic half outright and names the geometric one, so that after it the
residue of B2 is a single binder with no group theory left in it.

## The algebraic half, in one line each

If `t (g λ)^p t⁻¹ = (g μ)^q` with `p, q ≠ 0` then `g λ` and `g μ` are
commensurable in Dahmani--Guirardel--Osin's sense, so `λ = μ` by hypothesis; and
once `λ = μ` that same equation *is* membership of `t` in
`GGT.Elementary.elementaryClosure (g λ)`, whose defining predicate is exactly
"conjugates some nonzero power to some nonzero power".  Nothing is lost in
either step, which is why the elementary closure is the right family here and a
cyclic subgroup is not — `GGT/HullSCConeOffHeavyProperPower.lean` refutes the
cyclic choice, and this is the positive side of the same coin.

## Model tests

`PairwiseNonCommensurable` is tested from both ends.

At a one-element index type it holds vacuously
(`pairwiseNonCommensurable_of_subsingleton`) — there is no pair to separate,
which is the degenerate case and correctly carries no content.

At a constant family it **fails**, unconditionally and for every element:
`not_pairwiseNonCommensurable_const` takes `t = 1` and `p = q = 1`, where
`1 · h · 1⁻¹ = h` needs no hypothesis at all.  That is the test with content —
a predicate that accepted a constant family would let the same subgroup be
"separated from itself", and the whole point of the `λ = μ` conclusion is that
it cannot.

## What is left

`DiameterForcesConjugateCommonPower`, the geometric half.  Its analytic core is
already in the tree as
`HullGeometry.exists_common_zpow_of_forward_fellow_travel` — Lemma 6.7 in the
acylindrical form — which wants a geodesic space and therefore wants the
`PointQuot` model and the transfer pattern of
`GGT/HullSCConeOffHeavyModel.lean`.  What is owed on top of it is the passage
from `diam ≥ R` to long fellow-travel of the two translated quasi-axes, which is
where the Hausdorff distance between `E(h)(1)` and `⟨h⟩(1)` enters — the same
constant clause (a) currently carries as a hypothesis, so the two close
together.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Non-commensurability -/

/-- **Pairwise non-commensurability**, negating Dahmani--Guirardel--Osin's
"some nonzero powers are conjugate".  This is the hypothesis of their Theorem
6.8 and of Hull's Corollary 3.12, and it is what the `λ = μ` half of geometric
separation is bought with. -/
def PairwiseNonCommensurable {G : Type u} [Group G] {Λ : Type w} (g : Λ → G) :
    Prop :=
  ∀ lam mu : Λ, lam ≠ mu → ∀ p q : ℤ, p ≠ 0 → q ≠ 0 → ∀ t : G,
    t * (g lam) ^ p * t⁻¹ ≠ (g mu) ^ q

/-- **Model test, degenerate side.**  With at most one index there is no pair,
so the predicate holds and carries no content — which is correct. -/
theorem pairwiseNonCommensurable_of_subsingleton {G : Type u} [Group G]
    {Λ : Type w} [Subsingleton Λ] (g : Λ → G) : PairwiseNonCommensurable g := by
  intro lam mu hne
  exact absurd (Subsingleton.elim lam mu) hne

/-- **Model test, the one with content.**  A constant family is never pairwise
non-commensurable, for any element whatsoever: `t = 1` and `p = q = 1` give
`1 · h · 1⁻¹ = h` with no hypothesis on `h`.

A predicate that accepted a constant family would allow a subgroup to be
"geometrically separated from itself", which is exactly what the `λ = μ`
conclusion exists to forbid. -/
theorem not_pairwiseNonCommensurable_const {G : Type u} [Group G] (h : G) :
    ¬ PairwiseNonCommensurable (fun _ : Bool => h) := by
  intro hnc
  refine hnc false true (by decide) 1 1 one_ne_zero one_ne_zero 1 ?_
  rw [one_mul, inv_one, mul_one]

/-! ## The geometric half, named -/

/-- **The geometric residue of B2.**  The diameter hypothesis of geometric
separation forces a conjugate common power.

This is Dahmani--Guirardel--Osin's Lemma 6.7 together with the passage from
`diam ≥ R` to long oriented fellow-travelling of the two translated quasi-axes.
It is stated and not proved here; see the module header for what is available
towards it. -/
def DiameterForcesConjugateCommonPower {G : Type u} [Group G] {Λ : Type w}
    (A : Alphabet G) (g : Λ → G) : Prop :=
  ∀ eps : ℕ, ∃ R : ℕ, ∀ (t : G) (lam mu : Λ),
    (∀ D : ℕ, D < R → ∃ a b : G,
      a ∈ Elementary.elementaryClosure (g mu) ∧
      b ∈ Elementary.elementaryClosure (g mu) ∧
      D ≤ wordDist A.carrier a b ∧
      (∃ c : G, c ∈ Elementary.elementaryClosure (g lam) ∧
        wordDist A.carrier a (t * c) ≤ eps) ∧
      (∃ c : G, c ∈ Elementary.elementaryClosure (g lam) ∧
        wordDist A.carrier b (t * c) ≤ eps)) →
    ∃ p q : ℤ, p ≠ 0 ∧ q ≠ 0 ∧ t * (g lam) ^ p * t⁻¹ = (g mu) ^ q

/-! ## The algebraic half, proved -/

/-- **A conjugate common power gives both conclusions of geometric
separation.**

If `λ ≠ μ` the equation is exactly commensurability, which the hypothesis
forbids; and once `λ = μ` the same equation is, verbatim, the defining predicate
of `GGT.Elementary.elementaryClosure (g λ)`.

This is the step that makes the elementary closure the right family: for a
cyclic subgroup the second conclusion would be `t ∈ ⟨g λ⟩`, which the equation
does not give and which
`GGT/HullSCConeOffHeavyProperPower.lean` shows is genuinely false. -/
theorem eq_and_mem_elementaryClosure_of_conj_zpow {G : Type u} [Group G]
    {Λ : Type w} {g : Λ → G} (hncom : PairwiseNonCommensurable g)
    {lam mu : Λ} {t : G} {p q : ℤ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hconj : t * (g lam) ^ p * t⁻¹ = (g mu) ^ q) :
    lam = mu ∧ t ∈ Elementary.elementaryClosure (g lam) := by
  have hlm : lam = mu := by
    by_contra hne
    exact hncom lam mu hne p q hp hq t hconj
  subst hlm
  refine ⟨rfl, ?_⟩
  show ∃ n m : ℤ, n ≠ 0 ∧ m ≠ 0 ∧ t * (g lam) ^ n * t⁻¹ = (g lam) ^ m
  exact ⟨p, q, hp, hq, hconj⟩

/-! ## B2, reduced to its geometric half -/

/-- **The elementary closures of a pairwise non-commensurable family are
geometrically separated**, given the geometric half.

After this theorem the whole of B2 is `DiameterForcesConjugateCommonPower`:
there is no group theory left in the reduction, and the remaining content is the
quasi-axis argument. -/
theorem isGeometricallySeparated_elementaryClosure {G : Type u} [Group G]
    {Λ : Type w} (A : Alphabet G) (g : Λ → G)
    (hncom : PairwiseNonCommensurable g)
    (hgeo : DiameterForcesConjugateCommonPower A g) :
    IsGeometricallySeparated A (fun lam => Elementary.elementaryClosure (g lam)) := by
  intro eps
  obtain ⟨R, hR⟩ := hgeo eps
  refine ⟨R, ?_⟩
  intro t lam mu hdiam
  obtain ⟨p, q, hp, hq, hconj⟩ := hR t lam mu hdiam
  exact eq_and_mem_elementaryClosure_of_conj_zpow hncom hp hq hconj

end HullSC
end GroupApproximation
