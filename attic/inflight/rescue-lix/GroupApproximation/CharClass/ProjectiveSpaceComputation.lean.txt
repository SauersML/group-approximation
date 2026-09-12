import GroupApproximation.CharClass.ProjectiveSpaceInputs
import GroupApproximation.CharClass.ProjectiveSpaceRing
import GroupApproximation.CharClass.CohomologyDegreeZero
import GroupApproximation.CharClass.MayerVietorisSequence

/-!
# `H^*(ℂP^n; F₂)`, assembled

`hasCPCohomology_CP` is the unconditional statement: `H^*(ℂP^d;F₂)` is a line in
each even degree up to `2d` and zero elsewhere.  The conditional form
`hasCPCohomology_CPtop` is kept because it is the shape of the induction and is
what a different cover would be plugged into.

Its two hypotheses:

* `mv d`, a Mayer–Vietoris sequence for the cover of `ℂP^{d+1}` by the affine
  chart and the complement of the base point.  Their `mvSequence` for a general
  two-open cover instantiates it at `chartOpen d`, `punctOpen d`, whose union is
  `⊤` by `chartOpen_sup_punctOpen`.
* `hsum d`, that every class of `H^0` of the intersection is a sum of
  restrictions from the two pieces.  This is what kills the connecting map out of
  degree `0`, and with it `H^1(ℂP^{d+1})`.  It needs **no** identification of the
  Mayer–Vietoris restrictions with honest pullbacks: `exists_sum_eq_of_lines`
  derives it from exactness at `H^0(U) ⊕ H^0(V)` together with all four `H^0`
  groups being lines, by counting.

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
    (hsum : ∀ (d : ℕ) (w : Hmod2 (interSpace d) 0),
      ∃ (a : Hmod2 (chartSpace d) 0) (b : Hmod2 (punctSpace d) 0),
        (mv d).resWU 0 a + (mv d).resWV 0 b = w)
    (d : ℕ) : HasCPCohomology (CPtop d) d := by
  induction d with
  | zero => exact hasCPCohomology_zero
  | succ d ih =>
    exact hasCPCohomology_succ (mv d) d
      (hasPointCohomology_chartSpace d)
      (hasCPCohomology_punctSpace d ih)
      (hasSphereCohomology_interSpace d)
      (hsum d)
      ⟨cohZeroEquiv (CPtop (d + 1))⟩

/-- The degree-`2n` cohomology of `ℂP^d` is a line, for `n ≤ d`. -/
theorem cohomology_CPtop_line
    (mv : ∀ d : ℕ, MVSequence (CPtop (d + 1)) (chartSpace d) (punctSpace d) (interSpace d))
    (hsum : ∀ (d : ℕ) (w : Hmod2 (interSpace d) 0),
      ∃ (a : Hmod2 (chartSpace d) 0) (b : Hmod2 (punctSpace d) 0),
        (mv d).resWU 0 a + (mv d).resWV 0 b = w)
    (d n : ℕ) (hn : n ≤ d) :
    Nonempty (Hmod2 (CPtop d) (2 * n) ≃ₗ[ZMod 2] ZMod 2) :=
  (hasCPCohomology_CPtop mv hsum d).1 n hn

/-- Every other degree of `H^*(ℂP^d; F₂)` vanishes. -/
theorem cohomology_CPtop_eq_zero
    (mv : ∀ d : ℕ, MVSequence (CPtop (d + 1)) (chartSpace d) (punctSpace d) (interSpace d))
    (hsum : ∀ (d : ℕ) (w : Hmod2 (interSpace d) 0),
      ∃ (a : Hmod2 (chartSpace d) 0) (b : Hmod2 (punctSpace d) 0),
        (mv d).resWU 0 a + (mv d).resWV 0 b = w)
    (d k : ℕ) (hk : ∀ n : ℕ, n ≤ d → k ≠ 2 * n) (a : Hmod2 (CPtop d) k) : a = 0 :=
  (hasCPCohomology_CPtop mv hsum d).2 k hk a

/-- **The degree-2 generator** of `H^*(ℂP^d; F₂)` for `d ≥ 1`: the unique nonzero
class, which needs no orientation choice because an `F₂`-line has exactly one. -/
def cpGenerator
    (mv : ∀ d : ℕ, MVSequence (CPtop (d + 1)) (chartSpace d) (punctSpace d) (interSpace d))
    (hsum : ∀ (d : ℕ) (w : Hmod2 (interSpace d) 0),
      ∃ (a : Hmod2 (chartSpace d) 0) (b : Hmod2 (punctSpace d) 0),
        (mv d).resWU 0 a + (mv d).resWV 0 b = w)
    (d : ℕ) (hd : 1 ≤ d) : Hmod2 (CPtop d) 2 :=
  lineGen (K := ZMod 2) (by simpa using (cohomology_CPtop_line mv hsum d 1 hd).some)

/-- **The degree-zero hypothesis, from the line structure alone.**

Every class of `H^0(W)` is a sum of restrictions from `H^0(U)` and `H^0(V)`, as
soon as all four of `H^0` of the ambient space, the two opens and the
intersection are lines.  No identification of the Mayer–Vietoris restrictions
with honest pullbacks is needed, which is what makes the projective-space
computation independent of that identification.

If restriction from `U` does not kill the generator of `H^0(U)`, its image spans
`H^0(W)` and the required `a` is a scalar multiple of that generator — this is
where the restrictions being `K`-**linear** rather than merely additive is used,
and it is the whole reason the fields of `MVSequenceOf` carry linearity.
Likewise for `V`.  Otherwise both restrictions kill their generators, so
exactness at `H^0(U) ⊕ H^0(V)` produces classes `x`, `x'` on the ambient space
restricting to `(gen, 0)` and to `(0, gen)`.  Both are nonzero, so `x' = c • x`
with `c ≠ 0`, and then `0 = res_U x' = c • gen_U` contradicts the generator being
nonzero.

Over `F₂` the scalars are all `1` and this is the mod-2 counting argument the file
used to carry, verbatim. -/
theorem exists_sum_eq_of_lines {K : Type} [Field K] {X U V W : TopCat.{0}}
    (mv : MVSequenceOf K X U V W)
    (eX : Line K (Hmod K X 0)) (eU : Line K (Hmod K U 0))
    (eV : Line K (Hmod K V 0)) (eW : Line K (Hmod K W 0))
    (w : Hmod K W 0) :
    ∃ (a : Hmod K U 0) (b : Hmod K V 0), mv.resWU 0 a + mv.resWV 0 b = w := by
  by_cases hU0 : mv.resWU 0 (lineGen eU) = 0
  · by_cases hV0 : mv.resWV 0 (lineGen eV) = 0
    · -- both restrictions kill their generators; exactness gives two classes on `X`
      exfalso
      obtain ⟨x, hxU, hxV⟩ := (mv.exact_sum 0 (lineGen eU) 0).mp (by rw [hU0, map_zero])
      obtain ⟨x', hx'U, hx'V⟩ := (mv.exact_sum 0 0 (lineGen eV)).mp (by rw [hV0, map_zero])
      have hxne : x ≠ 0 := by
        intro h
        rw [h, map_zero] at hxU
        exact lineGen_ne_zero eU hxU.symm
      have hx'ne : x' ≠ 0 := by
        intro h
        rw [h, map_zero] at hx'V
        exact lineGen_ne_zero eV hx'V.symm
      obtain ⟨c, hc0, hc⟩ := exists_ne_zero_smul_of_line eX hxne hx'ne
      have hgen : c • lineGen eU = 0 := by
        rw [← hxU, ← map_smul, ← hc, hx'U]
      exact smul_ne_zero_of_line eU (lineGen_ne_zero eU) hc0 hgen
    · obtain ⟨c, hc⟩ := exists_smul_of_line eW hV0 w
      exact ⟨0, c • lineGen eV, by rw [map_zero, zero_add, map_smul, ← hc]⟩
  · obtain ⟨c, hc⟩ := exists_smul_of_line eW hU0 w
    exact ⟨c • lineGen eU, 0, by rw [map_zero, add_zero, map_smul, ← hc]⟩

/-- `H^0` of the punctured space is a line: it is homotopy equivalent to `ℂP^d`,
which is nonempty and path connected. -/
def punctCohZeroEquiv (d : ℕ) : Hmod2 (punctSpace d) 0 ≃ₗ[ZMod 2] ZMod 2 :=
  (pullEquivOfHomotopyEquiv (punctOpenHomotopyEquiv d) 0).symm.trans
    (cohZeroEquiv (CPtop d))

/-- **`H^*(ℂP^d; F₂)`, unconditionally.**  A line in `H^{2n}` for every `n ≤ d`,
and nothing in any other degree. -/
theorem hasCPCohomology_CP (d : ℕ) : HasCPCohomology (CPtop d) d :=
  hasCPCohomology_CPtop
    (fun d => mvSequence (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d))
    (fun d w => exists_sum_eq_of_lines _ (cohZeroEquiv (CPtop (d + 1)))
      (hasPointCohomology_chartSpace d).1.some (punctCohZeroEquiv d)
      (hasSphereCohomology_interSpace d).1.some w) d

end

end CharClass
end GroupApproximation
