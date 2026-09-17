import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableMilnor.Connecting
import GroupApproximation.Meta.AxiomGuard

/-!
# Milnor's exact sequence `K₂(R ⧸ I) → K₁(R, I) → K₁(R)`

Lane sk-leavitt-16, endpoint module (Milnor, *Introduction to algebraic K-theory*, Thm 6.2,
exactness at `K₁(R, I)`).

**Truth check.**  The lane target (`ker(K₁(R,I) → K₁(R)) ⊆ image ∂`) is true, and in fact the
equality `ker = range ∂` holds and is proved here, for any surjective ring map `f : R →+* S`
between associative unital rings (so for `R ⧸ I` with `I` two-sided):

* `⊆`: a class `[g]` with `g ∈ GL(R, ker f) ∩ E(R)` is `φ(s)` for some `s ∈ St(R)`
  (`stableProjection_range`); then `φ(f_* s) = f(g) = 1`, so `f_* s ∈ K₂(S)` and
  `∂ (f_* s) = [g]` by `connecting_apply`.
* `⊇`: `∂ y = [φ(s)]` with `φ(s) ∈ E(R)`.

The double ring `R ×_{R/I} R` of the lane route is not needed: the only non-formal input is
Steinberg quotient exactness `SteinbergGroup.ringMap_ker_eq_kernelRootClosure`, already in the
corpus.  `K₁(R, I)` is `GL(R, I) ⧸ E'(R, I)` with `E'` the `GL(R)`-normal closure of the
relative elementary units (see `RelativeKOne.lean`; it equals Milnor's `E(R, I)` by his
Lemma 4.3, which is not needed for, and not formalized in, this theorem).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation GroupApproximation.AlgebraicK

section Exact

variable {R S : Type*} [Ring R] [Ring S]

/-- **Exactness at `K₁(R, ker f)`**: `ker (K₁(R, ker f) → K₁(R)) = range (∂ : K₂(S) → K₁(R, ker f))`
for a surjective ring map `f : R →+* S`. -/
theorem relativeKOneToKOne_ker_eq_connecting_range (f : R →+* S) (hf : Function.Surjective f) :
    (relativeKOneToKOne f).ker = (connecting f hf).range := by
  apply le_antisymm
  · intro z hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective
      (s := (relativeElementaryColim f).subgroupOf (relativeGL f)) z
    have hz' : ((g : ClassicalGLColim R) : ClassicalGLColim R ⧸ elementaryColim R) = 1 :=
      MonoidHom.mem_ker.mp hz
    obtain ⟨s, hs⟩ :=
      mem_range_stableProjection_of_mem_elementaryColim R ((QuotientGroup.eq_one_iff _).mp hz')
    have hsK : s ∈ stableK2Lifts f := by
      refine Subgroup.mem_comap.mpr (MonoidHom.mem_ker.mpr ?_)
      rw [stableProjection_stableRingMap, hs]
      exact MonoidHom.mem_ker.mp g.2
    have hg : liftToRelativeGL f ⟨s, hsK⟩ = g := Subtype.ext hs
    refine MonoidHom.mem_range.mpr ⟨liftToK2 f ⟨s, hsK⟩, ?_⟩
    rw [connecting_apply, hg]
  · intro z hz
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hz
    obtain ⟨p, rfl⟩ := liftToK2_surjective f hf y
    rw [MonoidHom.mem_ker, connecting_apply, relativeKOneToKOne_mk]
    exact (QuotientGroup.eq_one_iff _).mpr
      (stableProjection_mem_elementaryColim R (p : stableSteinberg R))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeKOneToKOne_ker_eq_connecting_range

/-- The lane-shaped inclusion `ker (K₁(R, ker f) → K₁(R)) ⊆ image ∂`. -/
theorem relativeKOneToKOne_ker_le_connecting_range (f : R →+* S)
    (hf : Function.Surjective f) :
    (relativeKOneToKOne f).ker ≤ (connecting f hf).range :=
  (relativeKOneToKOne_ker_eq_connecting_range f hf).le

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeKOneToKOne_ker_le_connecting_range

/-- `∂` lands in `ker (K₁(R, ker f) → K₁(R))`: the composite `K₂(S) → K₁(R, ker f) → K₁(R)`
is trivial. -/
theorem relativeKOneToKOne_comp_connecting (f : R →+* S) (hf : Function.Surjective f)
    (y : stableK2 S) :
    relativeKOneToKOne f (connecting f hf y) = 1 :=
  MonoidHom.mem_ker.mp
    ((relativeKOneToKOne_ker_eq_connecting_range f hf).ge (MonoidHom.mem_range.mpr ⟨y, rfl⟩))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeKOneToKOne_comp_connecting

end Exact

section Ideal

variable {R : Type*} [Ring R]

/-- **Milnor, Theorem 6.2, exactness at `K₁(R, I)`** for a two-sided ideal `I`:
`ker (K₁(R, I) → K₁(R)) = ∂ (K₂(R ⧸ I))`, where `K₁(R, I)` is `relativeKOne` of the quotient
map `Ideal.Quotient.mk I`, whose kernel is `I`. -/
theorem stableK2_map_quotient_exact_eq (I : Ideal R) [I.IsTwoSided] :
    (relativeKOneToKOne (Ideal.Quotient.mk I)).ker
      = (connecting (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).range :=
  relativeKOneToKOne_ker_eq_connecting_range (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableK2_map_quotient_exact_eq

/-- **The lane endpoint**: `ker (K₁(R, I) → K₁(R)) ⊆ image (∂ : K₂(R ⧸ I) → K₁(R, I))`. -/
theorem stableK2_map_quotient_exact (I : Ideal R) [I.IsTwoSided] :
    (relativeKOneToKOne (Ideal.Quotient.mk I)).ker
      ≤ (connecting (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).range :=
  (stableK2_map_quotient_exact_eq I).le

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableK2_map_quotient_exact

end Ideal

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
