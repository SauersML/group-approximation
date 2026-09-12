import GroupApproximation.GGT.HullSCConeOffHeavyNonComm

/-!
# From a large diameter to two matched pairs of powers

`GGT/HullSCConeOffHeavyNonComm.lean` reduced B2 to one geometric statement,
`DiameterForcesConjugateCommonPower`: the diameter hypothesis of geometric
separation forces a conjugate common power.  Dahmani--Guirardel--Osin get that
from their Lemma 6.7 — long oriented fellow-travelling of two translated
quasi-axes forces commensurable conjugates — so the work between the two is to
turn `diam ≥ R` into fellow-travelling data.

That passage has three steps, and only the first has no geometry in it:

1. **Replace closure elements by powers.**  The four points the diameter
   hypothesis hands over lie in `E(g μ)` and `E(g λ)`, and each is within `ρ` of
   an honest power because `⟨g⟩` has finite index in `E(g)`.  What comes out is
   two long, endpoint-matched pairs of powers.
2. Endpoint-matched long segments fellow-travel throughout, by thinness.
3. Fellow-travelling orbits have a common power —
   `HullGeometry.exists_common_zpow_of_forward_fellow_travel`, which is Lemma 6.7
   in the acylindrical form and is already proved.

This module is step 1.  It is pure bookkeeping — four triangle inequalities and
one left-invariance — and it is separated out precisely because it is the part
that looks geometric and is not.  Steps 2 and 3 are where the hyperbolicity
enters.

## The `ρ` input

`ClosureNearPowers` is the Hausdorff bound between `E(g)(1)` and `⟨g⟩(1)`, in the
element vocabulary rather than the orbit one.  It is Dahmani--Guirardel--Osin's
`d_Hau(E(h)(s), ⟨h⟩(s)) < ∞`, which they get from `⟨h⟩` being of finite index in
`E(h)` (their Lemma 6.5), and it is the same constant that
`GGT/HullSCConeOffHeavyUnconditional.lean` currently carries as a hypothesis for
clause (a).  Closing it closes both at once, which is why it is stated here as
its own named predicate rather than inlined.

## Model tests

At `g = 1` the closure is everything that conjugates a nonzero power of `1` to a
nonzero power of `1` — that is, all of `G` — while the powers of `1` are just
`1`, so `ClosureNearPowers A 1 ρ` says `G` has diameter at most `ρ`.  That is
false for an infinite group with an unbounded metric and true for a bounded one,
which is the right behaviour: the predicate is a real constraint and not a
tautology.  `not_closureNearPowers_one` records the false direction against the
free group, so the predicate is known not to be vacuous.

The conclusion is stated with `R ≤ d + 2ρ` rather than `R - 2ρ ≤ d` on purpose:
natural subtraction truncates at zero, and the truncated form would be
vacuously true whenever `R ≤ 2ρ` — exactly the regime the consumer must avoid.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The Hausdorff input -/

/-- **Every element of the elementary closure is within `ρ` of a power.**

This is `d_Hau(E(g)(1), ⟨g⟩(1)) ≤ ρ` written on elements.  It is what finite
index of `⟨g⟩` in `E(g)` buys, and it is the same constant clause (a) of the
cone-off leaf carries as a hypothesis. -/
def ClosureNearPowers {G : Type u} [Group G] (A : Alphabet G) (g : G)
    (rho : ℕ) : Prop :=
  ∀ x ∈ Elementary.elementaryClosure g, ∃ k : ℤ,
    wordDist A.carrier x (g ^ k) ≤ rho

/-- **Model test: the predicate is not vacuous.**  At `g = 1` the elementary
closure is all of `G` — every `x` conjugates `1 ^ 1` to `1 ^ 1` — while the only
power of `1` is `1`, so the predicate collapses to "every element is within `ρ`
of `1`", which bounds the whole metric by `2ρ`.  The witness pair is therefore
taken at distance `2ρ + 1`, not `ρ + 1`: at `ρ + 1` the two triangle legs still
fit and nothing is contradicted. -/
theorem not_closureNearPowers_one (rho : ℕ) :
    ¬ ClosureNearPowers (GGT.freeGroupAlphabet (Fin 2)) 1 rho := by
  intro h
  obtain ⟨a, b, hab⟩ := unbounded_freeGroupAlphabet (2 * rho + 1)
  have hmem : b ∈ Elementary.elementaryClosure (1 : FreeGroup (Fin 2)) := by
    show ∃ n m : ℤ, n ≠ 0 ∧ m ≠ 0 ∧ b * (1 : FreeGroup (Fin 2)) ^ n * b⁻¹
      = (1 : FreeGroup (Fin 2)) ^ m
    exact ⟨1, 1, one_ne_zero, one_ne_zero, by simp⟩
  obtain ⟨k, hk⟩ := h b hmem
  rw [one_zpow] at hk
  have hzero : wordDist (GGT.freeGroupAlphabet (Fin 2)).carrier a b
      ≤ wordDist (GGT.freeGroupAlphabet (Fin 2)).carrier a 1
        + wordDist (GGT.freeGroupAlphabet (Fin 2)).carrier 1 b :=
    wordDist_triangle (GGT.freeGroupAlphabet (Fin 2)).symmetricGenerating a 1 b
  have hb1 : wordDist (GGT.freeGroupAlphabet (Fin 2)).carrier 1 b ≤ rho := by
    rw [wordDist_comm (GGT.freeGroupAlphabet (Fin 2)).symmetricGenerating]
    exact hk
  have hmema : a ∈ Elementary.elementaryClosure (1 : FreeGroup (Fin 2)) := by
    show ∃ n m : ℤ, n ≠ 0 ∧ m ≠ 0 ∧ a * (1 : FreeGroup (Fin 2)) ^ n * a⁻¹
      = (1 : FreeGroup (Fin 2)) ^ m
    exact ⟨1, 1, one_ne_zero, one_ne_zero, by simp⟩
  obtain ⟨k', hk'⟩ := h a hmema
  rw [one_zpow] at hk'
  omega

/-! ## Step 1: closure elements become powers -/

/-- **The diameter hypothesis, restated on powers.**

The four points geometric separation hands over lie in the two elementary
closures; each is within `ρ` of a power, so what comes out is a pair of powers
of `g μ` still far apart, each `ε + 2ρ`-close to a translate of a power of
`g λ`.  That is the endpoint-matched data Dahmani--Guirardel--Osin's Lemma 6.7
consumes.

Every step is a triangle inequality except one use of left invariance, which is
what turns `d(a, t·c) ≤ ε` together with `d(c, (g λ)^k) ≤ ρ` into
`d(a, t·(g λ)^k) ≤ ε + ρ`. -/
theorem exists_matched_powers_of_diam {G : Type u} [Group G] {Λ : Type w}
    (A : Alphabet G) (g : Λ → G) {rho eps R : ℕ} {t : G} {lam mu : Λ} {a b : G}
    (hclose : ∀ nu : Λ, ClosureNearPowers A (g nu) rho)
    (ha : a ∈ Elementary.elementaryClosure (g mu))
    (hb : b ∈ Elementary.elementaryClosure (g mu))
    (hab : R ≤ wordDist A.carrier a b)
    (hca : ∃ c : G, c ∈ Elementary.elementaryClosure (g lam) ∧
      wordDist A.carrier a (t * c) ≤ eps)
    (hcb : ∃ c : G, c ∈ Elementary.elementaryClosure (g lam) ∧
      wordDist A.carrier b (t * c) ≤ eps) :
    ∃ i j k l : ℤ,
      R ≤ wordDist A.carrier ((g mu) ^ i) ((g mu) ^ j) + 2 * rho ∧
      wordDist A.carrier ((g mu) ^ i) (t * (g lam) ^ k) ≤ eps + 2 * rho ∧
      wordDist A.carrier ((g mu) ^ j) (t * (g lam) ^ l) ≤ eps + 2 * rho := by
  have hS := A.symmetricGenerating
  obtain ⟨i, hi⟩ := hclose mu a ha
  obtain ⟨j, hj⟩ := hclose mu b hb
  obtain ⟨c, hcmem, hcd⟩ := hca
  obtain ⟨c', hc'mem, hc'd⟩ := hcb
  obtain ⟨k, hk⟩ := hclose lam c hcmem
  obtain ⟨l, hl⟩ := hclose lam c' hc'mem
  refine ⟨i, j, k, l, ?_, ?_, ?_⟩
  · -- the two powers are still far apart
    have t1 := wordDist_triangle hS a ((g mu) ^ i) b
    have t2 := wordDist_triangle hS ((g mu) ^ i) ((g mu) ^ j) b
    have hcomm : wordDist A.carrier ((g mu) ^ j) b
        = wordDist A.carrier b ((g mu) ^ j) := wordDist_comm hS _ _
    omega
  · -- the first power is close to a translate of a power of `g lam`
    have hshift : wordDist A.carrier (t * c) (t * (g lam) ^ k)
        = wordDist A.carrier c ((g lam) ^ k) := wordDist_left_invariant _ t _ _
    have t1 := wordDist_triangle hS ((g mu) ^ i) a (t * (g lam) ^ k)
    have t2 := wordDist_triangle hS a (t * c) (t * (g lam) ^ k)
    have hcomm : wordDist A.carrier ((g mu) ^ i) a
        = wordDist A.carrier a ((g mu) ^ i) := wordDist_comm hS _ _
    omega
  · -- and so is the second
    have hshift : wordDist A.carrier (t * c') (t * (g lam) ^ l)
        = wordDist A.carrier c' ((g lam) ^ l) := wordDist_left_invariant _ t _ _
    have t1 := wordDist_triangle hS ((g mu) ^ j) b (t * (g lam) ^ l)
    have t2 := wordDist_triangle hS b (t * c') (t * (g lam) ^ l)
    have hcomm : wordDist A.carrier ((g mu) ^ j) b
        = wordDist A.carrier b ((g mu) ^ j) := wordDist_comm hS _ _
    omega

end HullSC
end GroupApproximation
