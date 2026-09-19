import GroupApproximation.GGT.HullSCConeOffHeavyFellowTravel
import GroupApproximation.GGT.HullSCConeOffHeavyMatched

/-!
# B2 reduced to one uniform threshold

`GGT/HullSCConeOffHeavyMatched.lean` turned the diameter hypothesis of geometric
separation into two endpoint-matched pairs of powers, and
`GGT/HullSCConeOffHeavyFellowTravel.lean` proved that two long orbits from a
common basepoint with close ends share a nonzero power.  This module joins them,
and in doing so isolates the one thing that is still owed.

## What is owed, exactly

`MatchedPowersForceCommonPower` is Dahmani--Guirardel--Osin's Lemma 6.7 written
in the word metric, in the shape step 1 produces: *for every closeness budget
`B` there is a length `T` such that two `T`-separated powers of `g μ`, each
within `B` of a translate `t · (g λ)^•`, force a conjugate common power.*

The quantifier order is the whole content, and it is why
`exists_common_zpow_of_close_orbit_endpoints_zpow` does **not** discharge it.
That theorem produces its threshold *after* seeing the two elements, and the
second element here is `t (g λ) t⁻¹`, which varies with `t`, while geometric
separation must fix `R` before `t`.

What is **not** the obstruction is unboundedness, and it is worth saying so
because it looks like the obstruction.  Once `t` is constrained by the matching
hypothesis, every ingredient of the threshold in
`ElementaryMorse.exists_common_zpow_of_forward_fellow_travel_of_pairStab` is
uniformly bounded.  The displacement `dist z (b • z)` at a basepoint `z` on the
`g μ`-axis is at most `|g λ| + 2B`: `z` lies within `B` of a point `w` of the
`b`-orbit, and `dist w (b • w) = |g λ|` because conjugation does not change the
displacement along one's own axis.  The loxodromy constants of `b` at `z` are
those of `g λ` with the additive constant inflated by `2B`, by the same
comparison.  The pair-stabiliser bound is acylindricity's, which depends on `ε`
alone.  So the threshold is a bounded function of `t`-free data.

The obstruction is only that the theorem hides it: `T` is produced
existentially, after the elements are fixed, rather than exposed as a function
of `δ`, `C`, the two loxodromy constants, the two displacements and the
acylindricity bound.  Hoisting it is the same repair this lane already performed
for the Morse constants (`GGT/ElementaryMorseChord.lean`) — quantifier surgery
on an existing proof, not new geometry.  It belongs in the module that owns the
core, not here.

So `MatchedPowersForceCommonPower` is carried as an explicit hypothesis, and
`diameterForcesConjugateCommonPower_of_matchedPowers` below is the honest
statement of where B2 stands: everything except the uniform threshold is proved.

## Model tests

`matchedPowersForceCommonPower_of_bounded` checks that the quantifier order is
satisfiable at all: if the alphabet makes the whole group bounded, `T` may be
taken past the diameter and the hypothesis is unsatisfiable.  A statement that
even a bounded metric could not satisfy would be malformed rather than hard.

`not_conj_zpow_freeBasis` checks the other side, that the conclusion is not
free: at `t = 1` and two distinct basis elements of a free group there is no
conjugate common power at all.  So the predicate genuinely constrains the
family, and the two tests bracket it — one shows it is satisfiable, the other
that it is not automatic.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The uniform threshold -/

/-- **Dahmani--Guirardel--Osin's Lemma 6.7, in the word metric.**

For each closeness budget `B` there is a separation `T` past which two matched
pairs of powers force a conjugate common power.  `T` is chosen before `t`, which
is what geometric separation needs and what the pointwise fellow-travel theorems
do not give. -/
def MatchedPowersForceCommonPower {G : Type u} [Group G] {Λ : Type w}
    (A : Alphabet G) (g : Λ → G) : Prop :=
  ∀ B : ℕ, ∃ T : ℕ, ∀ (t : G) (lam mu : Λ) (i j k l : ℤ),
    T ≤ wordDist A.carrier ((g mu) ^ i) ((g mu) ^ j) →
    wordDist A.carrier ((g mu) ^ i) (t * (g lam) ^ k) ≤ B →
    wordDist A.carrier ((g mu) ^ j) (t * (g lam) ^ l) ≤ B →
    ∃ p q : ℤ, p ≠ 0 ∧ q ≠ 0 ∧ t * (g lam) ^ p * t⁻¹ = (g mu) ^ q

/-! ## Model tests -/

/-- **The quantifier order is satisfiable.**  A bounded word metric admits a
separation past its own diameter, so the hypothesis never fires.  All the
content of the predicate is in the unbounded case. -/
theorem matchedPowersForceCommonPower_of_bounded {G : Type u} [Group G]
    {Λ : Type w} (A : Alphabet G) (g : Λ → G) {D : ℕ}
    (hD : ∀ x y : G, wordDist A.carrier x y ≤ D) :
    MatchedPowersForceCommonPower A g := by
  intro _B
  refine ⟨D + 1, ?_⟩
  intro _t _lam mu i j _k _l hsep _ _
  exact absurd (hD ((g mu) ^ i) ((g mu) ^ j)) (by omega)

/-- **The conclusion is not automatic.**  Two distinct basis elements of a free
group have no conjugate common power at `t = 1`, so a family containing both is
constrained rather than served by the predicate. -/
theorem not_conj_zpow_freeBasis :
    ¬ ∃ p q : ℤ, p ≠ 0 ∧ q ≠ 0 ∧
      (1 : FreeGroup (Fin 2)) * (FreeGroup.of (0 : Fin 2)) ^ p
          * (1 : FreeGroup (Fin 2))⁻¹ = (FreeGroup.of (1 : Fin 2)) ^ q := by
  rintro ⟨p, q, hp, hq, heq⟩
  refine not_exists_common_zpow_free_basis ⟨p, q, hp, hq, ?_⟩
  simpa using heq

/-! ## B2, modulo the threshold -/

/-- **The geometric binder of B2, from the uniform threshold.**

Given the Hausdorff bound `ρ` between each `E(g ν)` and its powers, and the
uniform threshold, the diameter hypothesis of geometric separation delivers a
conjugate common power.  The passage is bookkeeping: instantiate the diameter
hypothesis just below its own bound, replace the four closure elements by powers
with `exists_matched_powers_of_diam`, and hand the result to the threshold.

The separation `R := T + 2ρ + 1` is forced rather than chosen.  Step 1 loses
`2ρ` replacing closure elements by powers, and the diameter hypothesis is stated
strictly (`∀ D < R`), so instantiating it at `T + 2ρ` is what makes the surviving
power separation exactly `T`.

With `GGT/HullSCConeOffHeavyNonComm.lean`'s `eq_and_mem_elementaryClosure_of_conj_zpow`
this closes B2: geometric separation of `{E(g λ)}` for a pairwise
non-commensurable family. -/
theorem diameterForcesConjugateCommonPower_of_matchedPowers {G : Type u}
    [Group G] {Λ : Type w} (A : Alphabet G) (g : Λ → G) {rho : ℕ}
    (hclose : ∀ nu : Λ, ClosureNearPowers A (g nu) rho)
    (hmp : MatchedPowersForceCommonPower A g) :
    DiameterForcesConjugateCommonPower A g := by
  intro eps
  obtain ⟨T, hT⟩ := hmp (eps + 2 * rho)
  refine ⟨T + 2 * rho + 1, ?_⟩
  intro t lam mu hdiam
  obtain ⟨a, b, ha, hb, hab, hca, hcb⟩ := hdiam (T + 2 * rho) (by omega)
  obtain ⟨i, j, k, l, hsep, hik, hjl⟩ :=
    exists_matched_powers_of_diam A g hclose ha hb hab hca hcb
  exact hT t lam mu i j k l (by omega) hik hjl

end HullSC
end GroupApproximation
