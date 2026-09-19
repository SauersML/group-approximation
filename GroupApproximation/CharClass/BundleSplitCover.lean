import GroupApproximation.CharClass.BundleLineIntert
import GroupApproximation.CharClass.BundleLocalOn

/-!
# Complex vector bundles in the projection model, XXXI: the cover of a
projective bundle by a splitting

If `p` splits as a sum of pairwise orthogonal rank-one summands `q l`, then over
`P(p)` each summand cuts out the open set where it does not kill the tautological
line, and those sets cover: a nonzero subprojection of a direct sum has a
nonzero component.

On each such set the tautological line **is** the pullback of that summand.  The
intertwiner is the summand itself, and the two hypotheses `lineIntertIso` needs
are precisely the definition of the set: `q` is a projection, so it carries its
own image into itself, and the set is exactly where it does not kill the line.
No partial isometry is constructed and no invertibility is used.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section SplitCover

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- The locus on `P(p)` where the summand `q` does not kill the tautological
line. -/
def lineOpenSet (p q : Bundle X ι) : Set (Proj p) :=
  {z | q (projPi p z) * tautLine p z ≠ 0}

theorem mem_lineOpenSet_iff {p q : Bundle X ι} {z : Proj p} :
    z ∈ lineOpenSet p q ↔ q (projPi p z) * tautLine p z ≠ 0 := Iff.rfl

/-- **It is open.** -/
theorem isOpen_lineOpenSet (p q : Bundle X ι) : IsOpen (lineOpenSet p q) := by
  have h : lineOpenSet p q
      = (fun z => q (projPi p z) * tautLine p z) ⁻¹' ({(0 : Matrix ι ι ℂ)}ᶜ) := rfl
  rw [h]
  exact IsOpen.preimage
    ((q.continuous.comp (projPi p).continuous).matrix_mul (tautLine p).continuous)
    isOpen_compl_singleton

/-! ### They cover -/

/-- **The sets cover `P(p)`.**  A nonzero subprojection of a sum has a nonzero
component. -/
theorem exists_mem_lineOpenSet (p : Bundle X ι) (r : ℕ) (q : ℕ → Bundle X ι)
    (hsum : ∀ x, p x = ∑ l ∈ Finset.range r, q l x) (z : Proj p) :
    ∃ l ∈ Finset.range r, z ∈ lineOpenSet p (q l) := by
  by_contra hcon
  have hall : ∀ l ∈ Finset.range r, q l (projPi p z) * tautLine p z = 0 := by
    intro l hl
    by_contra hne
    exact hcon ⟨l, hl, hne⟩
  have hzero : p (projPi p z) * tautLine p z = 0 := by
    rw [hsum, Finset.sum_mul]
    exact Finset.sum_eq_zero hall
  have habs : p (projPi p z) * tautLine p z = tautLine p z := tautLine_le p z
  rw [habs] at hzero
  have htr := trace_tautLine p z
  rw [hzero, Matrix.trace_zero] at htr
  exact zero_ne_one htr

theorem iUnion_lineOpenSet (p : Bundle X ι) (r : ℕ) (q : ℕ → Bundle X ι)
    (hsum : ∀ x, p x = ∑ l ∈ Finset.range r, q l x) :
    (⋃ l ∈ Finset.range r, lineOpenSet p (q l)) = (Set.univ : Set (Proj p)) := by
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨l, hl, hz⟩ := exists_mem_lineOpenSet p r q hsum z
  exact Set.mem_biUnion hl hz

/-! ### On each set the tautological line is the summand -/

/-- On `lineOpenSet p q` the summand does not kill a nonzero vector of the
tautological line.  This is the `hne` hypothesis of `lineIntertIso`, and it is
the defining condition of the set. -/
theorem mulVec_ne_zero_of_mem_lineOpenSet (p q : Bundle X ι) {z : Proj p}
    (hz : z ∈ lineOpenSet p q) {v : ι → ℂ}
    (hv : tautLine p z *ᵥ v = v) (hv0 : v ≠ 0) :
    q (projPi p z) *ᵥ v ≠ 0 := by
  obtain ⟨u, hu, hT⟩ := eq_rankOneProj_of_trace_one
    ((tautLine p).isStarProjection z) (trace_tautLine p z)
  have hqu : q (projPi p z) *ᵥ u ≠ 0 := by
    intro h0
    refine hz ?_
    rw [hT, mul_rankOneProj, h0]
    ext i j
    simp [Matrix.vecMulVec_apply]
  set c : ℂ := ∑ k, star (u k) * v k with hcdef
  have hvc : c • u = v := by
    rw [hcdef, ← rankOneProj_mulVec, ← hT, hv]
  have hc : c ≠ 0 := by
    intro h0
    refine hv0 ?_
    rw [← hvc, h0, zero_smul]
  rw [← hvc, Matrix.mulVec_smul]
  exact smul_ne_zero hc hqu

/-- **On `lineOpenSet p q` the tautological line is the pullback of `q`.**
The intertwiner is `q` itself; the two hypotheses are the definition of the
set. -/
noncomputable def tautLineIsoSummand (p q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) :
    BundleIso (restrictTo (tautLine p) (lineOpenSet p q))
      (restrictTo (comap (projPi p) q) (lineOpenSet p q)) :=
  lineIntertIso (fun y : ↥(lineOpenSet p q) => q (projPi p (y : Proj p)))
    ((q.continuous.comp (projPi p).continuous).comp continuous_subtype_val)
    (restrictTo (tautLine p) (lineOpenSet p q))
    (restrictTo (comap (projPi p) q) (lineOpenSet p q))
    (fun y => trace_tautLine p (y : Proj p))
    (fun y => hq (projPi p (y : Proj p)))
    (fun y v _ => q.mulVec_mulVec_self (projPi p (y : Proj p)) v)
    (fun y _ hv hv0 => mulVec_ne_zero_of_mem_lineOpenSet p q y.2 hv hv0)

end SplitCover

end Bundle

end CharClass
end GroupApproximation
