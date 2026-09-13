import GroupApproximation.Pestov91.LEF
import GroupApproximation.Algebra.CornerRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Corners of LEF rings are LEF

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1743–1747:

> The induced core is $C\cap Y$.  Indeed its return ring is a corner
> of the LEF ring $R_Y$, so it lies in the induced chain-recurrent core.
> Conversely, saturating that core through the finite towers gives a
> closed invariant subsystem whose ring is a corner of a matrix ring
> over an LEF ring, hence LEF.

Both halves of the printed argument pass LEF-ness to a corner `eRe`.  Given a finite subset `t` of
the corner, take a finite model `φ : R → F` on `{e} ∪ t`.  Then `φ e` is idempotent, and
`x ↦ φ e · φ x · φ e` is a finite model of `t` inside the corner `φ(e) F φ(e)`, whose unit is `φ e`.

* `Pestov91.IsLEFRing.corner`: if `R` is LEF, so is `Corner R e he`.
-/

namespace GroupApproximation

open MFQuotientUnits

/-- **A corner of an LEF ring is LEF.** -/
theorem Pestov91.IsLEFRing.corner {R : Type*} [Ring R] (hR : Pestov91.IsLEFRing R) (e : R)
    (he : IsIdempotentElem e) : Pestov91.IsLEFRing (Corner R e he) := by
  classical
  intro t
  obtain ⟨F, _, _, φ, hinj, h0, _, hops⟩ := hR (insert e (t.image Subtype.val))
  have hmem_e : e ∈ insert e (t.image Subtype.val) := Finset.mem_insert_self _ _
  have hmem : ∀ x ∈ t, (x : R) ∈ insert e (t.image Subtype.val) := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)
  have hφe : IsIdempotentElem (φ e) := by
    show φ e * φ e = φ e
    rw [← (hops e hmem_e e hmem_e).2, he.eq]
  have hleft : ∀ x ∈ t, φ e * φ (x : R) = φ (x : R) := fun x hx => by
    rw [← (hops e hmem_e _ (hmem x hx)).2, x.2.1]
  have hright : ∀ x ∈ t, φ (x : R) * φ e = φ (x : R) := fun x hx => by
    rw [← (hops _ (hmem x hx) e hmem_e).2, x.2.2]
  have hcorner : ∀ x ∈ t, φ e * φ (x : R) * φ e = φ (x : R) := fun x hx => by
    rw [hleft x hx, hright x hx]
  let ψ : Corner R e he → Corner F (φ e) hφe := fun x =>
    ⟨φ e * φ (x : R) * φ e,
      by rw [← mul_assoc, ← mul_assoc, hφe.eq],
      by rw [mul_assoc, hφe.eq]⟩
  refine ⟨Corner F (φ e) hφe, inferInstance, inferInstance, ψ, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have h : φ e * φ (x : R) * φ e = φ e * φ (y : R) * φ e := congrArg Subtype.val hxy
    rw [hcorner x hx, hcorner y hy] at h
    exact corner_ext (hinj (hmem x hx) (hmem y hy) h)
  · refine corner_ext ?_
    show φ e * φ 0 * φ e = 0
    rw [h0, mul_zero, zero_mul]
  · refine corner_ext ?_
    show φ e * φ e * φ e = φ e
    rw [hφe.eq, hφe.eq]
  · intro a ha b hb
    refine ⟨corner_ext ?_, corner_ext ?_⟩
    · show φ e * φ ((a : R) + (b : R)) * φ e = φ e * φ (a : R) * φ e + φ e * φ (b : R) * φ e
      rw [(hops _ (hmem a ha) _ (hmem b hb)).1, mul_add, add_mul]
    · show φ e * φ ((a : R) * (b : R)) * φ e =
        (φ e * φ (a : R) * φ e) * (φ e * φ (b : R) * φ e)
      rw [(hops _ (hmem a ha) _ (hmem b hb)).2, hcorner a ha, hcorner b hb, ← mul_assoc,
        hleft a ha, mul_assoc, hright b hb]

end GroupApproximation

#audit_axioms GroupApproximation.Pestov91.IsLEFRing.corner
