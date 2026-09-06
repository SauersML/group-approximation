import GroupApproximation.CharClass.ProjectiveSpaceInputs
import GroupApproximation.CharClass.ProjectiveSpaceRing
import GroupApproximation.CharClass.CohomologyDegreeZero

/-!
# `H^*(ℂP^n; F₂)`, assembled

Everything the induction needs is now in place except the Mayer–Vietoris sequence
itself, which is lane `cc-cohom-api`'s.  So the computation is stated here with
that sequence as a hypothesis: `hasCPCohomology_CPtop` is a theorem *today*, and
becomes the unconditional statement by supplying one term.

Two hypotheses, both from `cc-cohom-api`:

* `mv d`, a Mayer–Vietoris sequence for the cover of `ℂP^{d+1}` by the affine
  chart and the complement of the base point.  Their `mvSequence` for a general
  two-open cover instantiates it at `chartOpen d`, `punctOpen d`, whose union is
  `⊤` by `chartOpen_sup_punctOpen`.
* `hres d`, that restriction `H^0(chart) → H^0(chart ∩ punctured)` is onto.  Both
  groups are lines and restriction sends `1` to `1`, so this reduces to
  `one ≠ 0` in `H^0` of a nonempty space, which is the small lemma also requested
  from that lane.  It is what kills the connecting map out of degree `0`, and
  with it `H^1(ℂP^{d+1})`.

The conclusion is `HasCPCohomology (CPtop d) d`: a line in `H^{2n}` for every
`n ≤ d`, and nothing in any other degree.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

noncomputable section

/-- **The mod-2 cohomology of complex projective space.**

By induction on `d`.  The base case is that `ℂP^0` is a point.  Each step is one
application of `hasCPCohomology_succ` to the cover of `ℂP^{d+1}` by the affine
chart, which is contractible, and the complement of the base point, which
deformation retracts onto `ℂP^d`; the two meet in `S^{2d+1}`. -/
theorem hasCPCohomology_CPtop
    (mv : ∀ d : ℕ, MVSequence (CPtop (d + 1)) (chartSpace d) (punctSpace d) (interSpace d))
    (hres : ∀ d : ℕ, Function.Surjective ((mv d).resWU 0))
    (d : ℕ) : HasCPCohomology (CPtop d) d := by
  induction d with
  | zero => exact hasCPCohomology_zero
  | succ d ih =>
    exact hasCPCohomology_succ (mv d) d
      (hasPointCohomology_chartSpace d)
      (hasCPCohomology_punctSpace d ih)
      (hasSphereCohomology_interSpace d)
      (hres d)
      ⟨cohZeroEquiv (CPtop (d + 1))⟩

/-- The degree-`2n` cohomology of `ℂP^d` is a line, for `n ≤ d`. -/
theorem cohomology_CPtop_line
    (mv : ∀ d : ℕ, MVSequence (CPtop (d + 1)) (chartSpace d) (punctSpace d) (interSpace d))
    (hres : ∀ d : ℕ, Function.Surjective ((mv d).resWU 0))
    (d n : ℕ) (hn : n ≤ d) :
    Nonempty (Hmod2 (CPtop d) (2 * n) ≃ₗ[ZMod 2] ZMod 2) :=
  (hasCPCohomology_CPtop mv hres d).1 n hn

/-- Every other degree of `H^*(ℂP^d; F₂)` vanishes. -/
theorem cohomology_CPtop_eq_zero
    (mv : ∀ d : ℕ, MVSequence (CPtop (d + 1)) (chartSpace d) (punctSpace d) (interSpace d))
    (hres : ∀ d : ℕ, Function.Surjective ((mv d).resWU 0))
    (d k : ℕ) (hk : ∀ n : ℕ, n ≤ d → k ≠ 2 * n) (a : Hmod2 (CPtop d) k) : a = 0 :=
  (hasCPCohomology_CPtop mv hres d).2 k hk a

/-- **The degree-2 generator** of `H^*(ℂP^d; F₂)` for `d ≥ 1`: the unique nonzero
class, which needs no orientation choice because an `F₂`-line has exactly one. -/
def cpGenerator
    (mv : ∀ d : ℕ, MVSequence (CPtop (d + 1)) (chartSpace d) (punctSpace d) (interSpace d))
    (hres : ∀ d : ℕ, Function.Surjective ((mv d).resWU 0))
    (d : ℕ) (hd : 1 ≤ d) : Hmod2 (CPtop d) 2 :=
  lineGen (by simpa using (cohomology_CPtop_line mv hres d 1 hd).some)

/-- **The remaining hypothesis, reduced to one equation.**  Both `H^0` groups are
lines, so restriction is onto as soon as it does not kill the unit; over `F₂` a
map hitting the unique nonzero element of a two-element group is onto. -/
theorem surjective_resWU_zero_of_one {X U V W : TopCat.{0}} (mv : MVSequence X U V W)
    [Nonempty ↥W] (hW : Nonempty (Hmod2 W 0 ≃ₗ[ZMod 2] ZMod 2))
    (h1 : mv.resWU 0 (one U) = one W) : Function.Surjective (mv.resWU 0) := by
  intro w
  rcases eq_zero_or_eq_of_line hW.some (one_ne_zero_cohZero W) w with hw | hw
  · exact ⟨0, by rw [map_zero, hw]⟩
  · exact ⟨one U, by rw [h1, hw]⟩

end

end CharClass
end GroupApproximation
