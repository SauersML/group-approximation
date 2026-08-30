import GroupApproximation.Analysis.VoiculescuOneStep

/-!
# (V4) and (V5): the absorption theorem and its Calkin corollary

`Analysis/VoiculescuOneStep` carries the one-step approximation, and this module
carries the two statements above it: the absorption theorem the assembly produces
from it, and the corollary the Enders--Shulman construction consumes.  Neither is
discharged here; what is proved is the algebra that connects them to their
consumers, and the checks that neither hypothesis list is degenerate.

## (V4), in the form the assembly produces

The plan describes the assembly as producing a unitary equivalence between `σ`
and `σ ⊕ ρ` modulo the compacts.  That form needs the direct sum `H ⊕ K` as a
Hilbert space, and the statement below avoids it, because what the assembly
literally builds is an *isometry*: iterating the one-step approximation along a
dense sequence with summable tolerances and mutually orthogonal ranges gives an
isometry `W : K → H` with `σ(a)W - Wρ(a)` compact for every `a` — that is, `ρ` is
a subrepresentation of `σ` modulo the compacts.  The `σ ⊕ ρ ≃ σ` form is a
consequence of that one and adds the direct sum back; the containment form is
what the iteration produces and is enough for everything below it.

`isCompactOperator_compress_sub` is the exchange between the intertwining form
and the compression form the one-step approximation speaks in: `W⋆σ(a)W - ρ(a)`
is `W⋆` times the intertwining defect, and the compacts are an ideal.

## (V5), and one hypothesis that is not needed

The plan states the Calkin corollary for two unital *faithful essential*
representations.  Faithfulness is not an extra hypothesis:
`injective_of_essential` derives it from essentiality, since `σ(a) = 0` is
compact.  So `CalkinUniquenessStatement` below asks only for essentiality, and
asking for faithfulness as well would ask a consumer to discharge something it
gets for free.

## The hypotheses are not vacuous

`absorption_not_finiteDimensional` is the model test, and it is the same one that
`Analysis/VoiculescuGlimmStatement` runs: an essential representation of a
nontrivial algebra forces `H` to be infinite-dimensional, since `σ(1) = 1` and in
finite dimensions `1` is compact.  Together with `injective_of_essential` this
says essentiality is doing real work in both statements rather than being
implied by the rest.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

/-! ## Essentiality, and what it already implies -/

/-- **An essential representation is faithful.**  `σ(a) = 0` is compact, so
essentiality sends `a` to `0`.  This is why the statements below carry only the
essentiality hypothesis: the "faithful" of the printed statement of Voiculescu's
corollary is a consequence, not an assumption. -/
theorem injective_of_essential {C H : Type} [CStarAlgebra C]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (sigma : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hess : ∀ a : C, IsCompactOperator (sigma a) → a = 0) :
    Function.Injective sigma := by
  refine (injective_iff_map_eq_zero sigma).mpr fun a ha ↦ hess a ?_
  rw [ha]
  exact isCompactOperator_zero

/-- **The model test.**  An essential unital representation of a nontrivial
algebra lives only on an infinite-dimensional space: `σ(1) = 1`, and in finite
dimensions the identity is compact, so essentiality would force `1 = 0`. -/
theorem absorption_not_finiteDimensional {C H : Type} [CStarAlgebra C]
    [Nontrivial C] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (sigma : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hess : ∀ a : C, IsCompactOperator (sigma a) → a = 0) :
    ¬ FiniteDimensional ℂ H := by
  intro hfin
  haveI : ProperSpace H := FiniteDimensional.proper ℂ H
  have hcpt : IsCompactOperator ((1 : H →L[ℂ] H) : H → H) :=
    isCompactOperator_id_iff_locallyCompactSpace.mpr inferInstance
  have hone : IsCompactOperator (sigma 1) := by rw [map_one]; exact hcpt
  exact one_ne_zero (hess 1 hone)

/-! ## The two statements -/

/-- **(V4) Voiculescu's absorption theorem, in the containment form the assembly
produces.**  An essential representation of a separable C⋆-algebra on a separable
Hilbert space contains, modulo the compacts, every representation on a separable
Hilbert space. -/
def AbsorptionContainmentStatement : Prop :=
  ∀ (C : Type) [CStarAlgebra C] [TopologicalSpace.SeparableSpace C]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H]
    (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      [TopologicalSpace.SeparableSpace K]
    (sigma : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (rho : C →⋆ₐ[ℂ] (K →L[ℂ] K)),
      (∀ a : C, IsCompactOperator (sigma a) → a = 0) →
        ∃ W : K →L[ℂ] H, ContinuousLinearMap.adjoint W ∘L W = 1 ∧
          ∀ a : C, IsCompactOperator (sigma a ∘L W - W ∘L rho a)

/-- **(V5) The Calkin corollary.**  Two essential representations of a separable
C⋆-algebra on the same separable Hilbert space have unitarily equivalent images
in the Calkin algebra, stated as compactness of the difference so that no
quotient structure is named. -/
def CalkinUniquenessStatement : Prop :=
  ∀ (C : Type) [CStarAlgebra C] [TopologicalSpace.SeparableSpace C]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H]
    (sigma tau : C →⋆ₐ[ℂ] (H →L[ℂ] H)),
      (∀ a : C, IsCompactOperator (sigma a) → a = 0) →
      (∀ a : C, IsCompactOperator (tau a) → a = 0) →
        ∃ u : H →L[ℂ] H, u ∈ unitary (H →L[ℂ] H) ∧
          ∀ a : C, IsCompactOperator (u * sigma a * star u - tau a)

/-! ## The intertwining form and the compression form -/

/-- **The exchange.**  Along an isometry, a compact intertwining defect gives a
compact compression defect: `W⋆σ(a)W - ρ(a)` is `W⋆` applied to
`σ(a)W - Wρ(a)`, and the compacts absorb the left factor.  This is how (V4)
reaches the compression language of the one-step approximation. -/
theorem isCompactOperator_compress_sub {K H : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {W : K →L[ℂ] H}
    (hW : ContinuousLinearMap.adjoint W ∘L W = 1) {S : H →L[ℂ] H} {R : K →L[ℂ] K}
    (h : IsCompactOperator (S ∘L W - W ∘L R)) :
    IsCompactOperator (ContinuousLinearMap.adjoint W ∘L S ∘L W - R) := by
  have hcancel : ContinuousLinearMap.adjoint W ∘L (W ∘L R) = R := by
    rw [← ContinuousLinearMap.comp_assoc, hW, ← ContinuousLinearMap.mul_def, one_mul]
  have hkey : ContinuousLinearMap.adjoint W ∘L (S ∘L W - W ∘L R)
      = ContinuousLinearMap.adjoint W ∘L S ∘L W - R := by
    rw [ContinuousLinearMap.comp_sub, hcancel]
  have hc := h.clm_comp (ContinuousLinearMap.adjoint W)
  rw [← ContinuousLinearMap.coe_comp, hkey] at hc
  exact hc

/-- **(V4) in compression form.**  The isometry the absorption theorem produces
compresses `σ` to `ρ` modulo the compacts, which is the shape the one-step
approximation the assembly runs on speaks in. -/
theorem compress_of_absorption (h : AbsorptionContainmentStatement)
    (C : Type) [CStarAlgebra C] [TopologicalSpace.SeparableSpace C]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H]
    (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      [TopologicalSpace.SeparableSpace K]
    (sigma : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (rho : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hess : ∀ a : C, IsCompactOperator (sigma a) → a = 0) :
    ∃ W : K →L[ℂ] H, ContinuousLinearMap.adjoint W ∘L W = 1 ∧
      ∀ a : C, IsCompactOperator
        (ContinuousLinearMap.adjoint W ∘L sigma a ∘L W - rho a) := by
  obtain ⟨W, hWiso, hWint⟩ := h C H K sigma rho hess
  exact ⟨W, hWiso, fun a ↦ isCompactOperator_compress_sub hWiso (hWint a)⟩

/-- **The absorption theorem embeds the second space in the first.**  Its
conclusion contains an isometry `K → H`, which is why `K` carries a separability
hypothesis: without one the statement would assert that a nonseparable space
embeds isometrically into a separable one. -/
theorem isometry_of_absorption (h : AbsorptionContainmentStatement)
    (C : Type) [CStarAlgebra C] [TopologicalSpace.SeparableSpace C]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H]
    (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      [TopologicalSpace.SeparableSpace K]
    (sigma : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (rho : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hess : ∀ a : C, IsCompactOperator (sigma a) → a = 0) :
    ∃ W : K →L[ℂ] H, Isometry W := by
  obtain ⟨W, hWiso, -⟩ := h C H K sigma rho hess
  exact ⟨W, (ContinuousLinearMap.isometry_iff_adjoint_comp_self W).mpr hWiso⟩

end

end ShulmanFill
end GroupApproximation
