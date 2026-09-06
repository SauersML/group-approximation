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
  lineGen (by simpa using (cohomology_CPtop_line mv hsum d 1 hd).some)

/-- **The degree-zero hypothesis, from counting alone.**

Every class of `H^0(W)` is a sum of restrictions from `H^0(U)` and `H^0(V)`, as
soon as all four of `H^0` of the ambient space, the two opens and the
intersection are lines.  No identification of the Mayer–Vietoris restrictions
with honest pullbacks is needed, which is what makes the projective-space
computation independent of that identification.

The argument is a count.  If restriction from `U` hits the generator of `H^0(W)`
we are done, and likewise for `V`.  Otherwise both restrictions kill their
generators, so exactness at `H^0(U) ⊕ H^0(V)` produces classes on the ambient
space restricting to `(gen, 0)` and to `(0, gen)`.  Both are nonzero, hence both
are *the* generator of `H^0(X)`, hence equal — but one restricts to the generator
of `H^0(U)` and the other to zero. -/
theorem exists_sum_eq_of_lines {X U V W : TopCat.{0}} (mv : MVSequence X U V W)
    (eX : Hmod2 X 0 ≃ₗ[ZMod 2] ZMod 2) (eU : Hmod2 U 0 ≃ₗ[ZMod 2] ZMod 2)
    (eV : Hmod2 V 0 ≃ₗ[ZMod 2] ZMod 2) (eW : Hmod2 W 0 ≃ₗ[ZMod 2] ZMod 2)
    (w : Hmod2 W 0) :
    ∃ (a : Hmod2 U 0) (b : Hmod2 V 0), mv.resWU 0 a + mv.resWV 0 b = w := by
  rcases eq_zero_or_eq_of_line eW (lineGen_ne_zero eW) w with hw | hw
  · exact ⟨0, 0, by rw [map_zero, map_zero, add_zero, hw]⟩
  subst hw
  rcases eq_zero_or_eq_of_line eW (lineGen_ne_zero eW) (mv.resWU 0 (lineGen eU)) with hU0 | hU0
  · rcases eq_zero_or_eq_of_line eW (lineGen_ne_zero eW) (mv.resWV 0 (lineGen eV)) with hV0 | hV0
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
      have hxx : x = x' := by
        rw [eq_lineGen_of_ne_zero eX hxne, eq_lineGen_of_ne_zero eX hx'ne]
      rw [hxx, hx'U] at hxU
      exact lineGen_ne_zero eU hxU.symm
    · exact ⟨0, lineGen eV, by rw [map_zero, zero_add, hV0]⟩
  · exact ⟨lineGen eU, 0, by rw [map_zero, add_zero, hU0]⟩

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
