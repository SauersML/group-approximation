import GroupApproximation.Kazhdan.HilbertCircumcenter
import GroupApproximation.Kazhdan.KazhdanFixedSpace

/-!
# The Hilbert-space circumcenter route to a translation-fixed vector

This module supplies the fixed-point engine that item 3 of Step 3 of the
printed proof of Proposition `\ref{prop:literal-base-T}` named:

> *"The orbit of `p` under the translation subgroup is bounded, so the
> Hilbert-space circumcenter argument gives a translation-fixed vector `q`
> with `‖q-p‖ ≤ 1/8`."*

**That proof is no longer printed.**  Commit `3a45fa60` ("Editorial pass:
rewrite orbit collapse, cut what nothing uses") replaced the three-step
property-`(T)` argument with a citation: `\ref{prop:literal-base-T}` now proves
its statement from `\ref{rem:classical-base}` and `\cite[Example~1.7.4(i)]{BHV}`
in a single paragraph, and the proposition's own statement is untouched.  The
quotation above is therefore a record of the deleted text.  The mathematics
below is unaffected and still supports the badged bridge declaration, but no
badge is owed on the circumcenter step itself, because no such step is printed.

The *circumcenter* of a bounded set is the centre of its smallest enclosing
ball — the unique minimizer of the covering radius.  That object, together
with its existence and uniqueness in a complete real inner product space, is
already developed in `Kazhdan/HilbertCircumcenter.lean`
(`Circumcenter.coveringRadius`, `Circumcenter.chebyshevRadius`,
`Circumcenter.existsUnique_center`).  What was missing on the
`prop:literal-base-T` path is only the *quantitative* corollary: the
circumcenter of a bounded orbit is not merely fixed, it lies inside every
closed ball around the base point that already contains the orbit.  That is
immediate, because the base point is itself a member of its own orbit, so its
distance to the circumcenter is at most the circumcenter's covering radius,
which is at most the covering radius at the base point.

Nothing here duplicates the closed-convex-hull development of
`Kazhdan/HilbertConvexFixedPoint.lean`: that file takes the minimal-norm point
of the closed convex hull of the orbit (the Hilbert projection / Bruhat–Tits
construction), which is a *different* point produced by a *different*
argument.  It remains available as the alternate route;
`exists_near_fixedSubspace_circumcenter` below is a signature-compatible
drop-in replacement realizing the printed one.
-/

namespace GroupApproximation
namespace P13CircumcenterRoute

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Circumcenters of bounded sets, quantitatively -/

omit [InnerProductSpace ℝ E] in
/-- A point of a bounded set lies within any radius that already covers the
set from a member of it — in particular the circumcenter of a bounded set
containing `x` is within `delta` of `x` as soon as the set lies in the closed
`delta`-ball about `x`. -/
theorem dist_center_le_of_covered {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) {c x : E} {delta : ℝ}
    (hc : Circumcenter.coveringRadius S c = Circumcenter.chebyshevRadius S)
    (hxS : x ∈ S) (hcover : ∀ s ∈ S, dist x s ≤ delta) :
    dist c x ≤ delta := by
  have hcenter : Circumcenter.coveringRadius S c ≤ delta := by
    rw [hc]
    exact (Circumcenter.chebyshevRadius_le hne hbdd x).trans
      (Circumcenter.coveringRadius_le hne hcover)
  exact (Circumcenter.dist_le_coveringRadius hbdd c hxS).trans hcenter

/-- Two points realizing the Chebyshev radius of a nonempty bounded set in a
complete real inner product space coincide: this is the uniqueness half of
`Circumcenter.existsUnique_center`, in the form used to prove invariance. -/
theorem eq_center_of_coveringRadius_eq [CompleteSpace E] {S : Set E}
    (hne : S.Nonempty) (hbdd : Bornology.IsBounded S) {c c' : E}
    (hc : Circumcenter.coveringRadius S c = Circumcenter.chebyshevRadius S)
    (hc' : Circumcenter.coveringRadius S c' = Circumcenter.chebyshevRadius S) :
    c' = c := by
  obtain ⟨d, -, hd⟩ := Circumcenter.existsUnique_center hne hbdd
  exact (hd c' hc').trans (hd c hc).symm

/-- **The circumcenter is fixed by every isometry preserving the set.**  This
is the invariance step of the circumcenter argument: covering radii are
transported by isometries, so the image of the circumcenter again realizes the
Chebyshev radius, and uniqueness identifies the two. -/
theorem center_fixed [CompleteSpace E] {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) {c : E}
    (hc : Circumcenter.coveringRadius S c = Circumcenter.chebyshevRadius S)
    {f : E → E} (hf : Isometry f) (hfS : f '' S = S) : f c = c := by
  refine eq_center_of_coveringRadius_eq hne hbdd hc ?_
  calc
    Circumcenter.coveringRadius S (f c) =
        Circumcenter.coveringRadius (f '' S) (f c) := by rw [hfS]
    _ = Circumcenter.coveringRadius S c :=
      Circumcenter.coveringRadius_image hf S c
    _ = Circumcenter.chebyshevRadius S := hc

/-! ## The orbit of a vector under a subgroup of an orthogonal representation -/

/-- The base point belongs to its own orbit. -/
theorem mem_orbit_self (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    x ∈ Set.range fun h : H ↦ rho h.1 x := by
  refine ⟨1, ?_⟩
  simp

/-- The orbit of a vector under a subgroup is nonempty. -/
theorem orbit_nonempty (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    (Set.range fun h : H ↦ rho h.1 x).Nonempty :=
  ⟨x, mem_orbit_self rho H x⟩

/-- **The orbit is bounded.**  This is the hypothesis the printed step opens
with: a uniform displacement bound over the subgroup puts the whole orbit in a
closed ball about the base point. -/
theorem isBounded_orbit (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E)
    {delta : ℝ} (hbound : ∀ h : H, ‖rho h.1 x - x‖ ≤ delta) :
    Bornology.IsBounded (Set.range fun h : H ↦ rho h.1 x) := by
  have hball : (Set.range fun h : H ↦ rho h.1 x) ⊆
      Metric.closedBall x delta := by
    rintro y ⟨h, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa only [norm_sub_rev] using hbound h
  exact (Metric.isBounded_closedBall (x := x) (r := delta)).subset hball

/-- The orbit is stable under the subgroup. -/
theorem orbit_image_eq (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E)
    (h : H) :
    (rho h.1) '' (Set.range fun k : H ↦ rho k.1 x) =
      Set.range fun k : H ↦ rho k.1 x := by
  ext y
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨h * k, ?_⟩
    simp
  · rintro ⟨k, rfl⟩
    refine ⟨rho (h⁻¹ * k).1 x, ⟨h⁻¹ * k, rfl⟩, ?_⟩
    simp

/-! ## The circumcenter fixed-point theorem, with the displacement bound -/

/-- **The Hilbert-space circumcenter argument.**  If every element of a
subgroup `H` displaces `x` by at most `delta`, then the circumcenter `q` of the
`H`-orbit of `x` — the centre of the smallest enclosing ball of that orbit — is
fixed by `H` and satisfies `‖q - x‖ ≤ delta`.

The conclusion records that `q` really is the circumcenter (it realizes the
Chebyshev radius of the orbit), so that consumers cannot mistake it for the
minimal-norm point of the closed convex hull. -/
theorem exists_circumcenter_fixed_norm_sub_le [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) {delta : ℝ}
    (hbound : ∀ h : H, ‖rho h.1 x - x‖ ≤ delta) :
    ∃ q : E,
      Circumcenter.coveringRadius (Set.range fun h : H ↦ rho h.1 x) q =
          Circumcenter.chebyshevRadius (Set.range fun h : H ↦ rho h.1 x) ∧
        (∀ h : H, rho h.1 q = q) ∧ ‖q - x‖ ≤ delta := by
  have hne : (Set.range fun h : H ↦ rho h.1 x).Nonempty :=
    orbit_nonempty rho H x
  have hbdd : Bornology.IsBounded (Set.range fun h : H ↦ rho h.1 x) :=
    isBounded_orbit rho H x hbound
  obtain ⟨c, hc, -⟩ := Circumcenter.existsUnique_center hne hbdd
  refine ⟨c, hc, ?_, ?_⟩
  · intro h
    exact center_fixed hne hbdd hc (rho h.1).isometry (orbit_image_eq rho H x h)
  · have hdist : dist c x ≤ delta := by
      refine dist_center_le_of_covered hne hbdd hc (mem_orbit_self rho H x) ?_
      rintro y ⟨h, rfl⟩
      rw [dist_eq_norm]
      simpa only [norm_sub_rev] using hbound h
    rwa [dist_eq_norm] at hdist

/-- **Circumcenter form of the near-fixed-subspace lemma.**  Signature-identical
to `HilbertConvexFixedPoint.exists_near_fixedSubspace`, but the witness is the
circumcenter of the orbit rather than the minimal-norm point of its closed
convex hull, so this is the lemma the manuscript's Step 3 names. -/
theorem exists_near_fixedSubspace_circumcenter [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) {delta : ℝ}
    (hbound : ∀ h : H, ‖rho h.1 x - x‖ ≤ delta) :
    ∃ y ∈ KazhdanFixedSpace.fixedSubspace rho H, ‖y - x‖ ≤ delta := by
  obtain ⟨q, -, hqfix, hqnear⟩ :=
    exists_circumcenter_fixed_norm_sub_le rho H x hbound
  exact ⟨q, (KazhdanFixedSpace.mem_fixedSubspace_iff rho H q).2
    (fun h hh ↦ hqfix ⟨h, hh⟩), hqnear⟩

end P13CircumcenterRoute
end GroupApproximation
