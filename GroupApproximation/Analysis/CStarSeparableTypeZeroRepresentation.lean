import GroupApproximation.Analysis.CStarHilbertCountableBasis
import GroupApproximation.Analysis.CStarInfiniteDimensionalGNS
import GroupApproximation.Analysis.CStarHilbertTransport
import GroupApproximation.Analysis.CStarSeparableFaithfulRepresentation
import GroupApproximation.Analysis.CStarTakesakiDense
import GroupApproximation.Analysis.ShulmanFillNormingRecognitionWiring

/-!
# Gelfand--Naimark on a separable Hilbert space in `Type 0`

`ShulmanFill.SeparableFaithfulRepresentationStatement` was the last cited input
of the recognition route.  This module proves it, and then restates the
conclusion of `ShulmanFill.conjugateWordNorming_of_printedPair_of_compatible`
with that hypothesis discharged, so the route comes to rest on the two Props the
manuscript itself cites and on nothing else.

The statement is delicate in exactly one respect and it is a universe one: the
algebra may be large --- the only one it is applied to is
`UniversalCStarAmalgam gamma gamma`, which sits one universe above `C` and `D`
--- while the Hilbert space must be in `Type 0`, because that is what the
amalgam machinery consumes.  So the GNS space, which lives in the algebra's
universe, cannot be handed over directly; it has to be replaced by an isometric
copy that is small, and that is the whole content of the descent.

## The route

* `Analysis/CStarSeparableFaithfulRepresentation` gives a countable separating
  family of states and the faithful diagonal GNS representation on
  `lp (fun n ↦ (ψ n).GNSSpace) 2`.
* The family `lp.single 2 n (gnsCoe (ψ n) b)`, over `n : ℕ` and `b` in a
  countable dense subset of the algebra, is countable and has trivial orthogonal
  complement --- that is `orthogonal_span_eq_bot_of_forall` fed by two appeals to
  `Continuous.ext_on`, once along the dense subset and once along the dense
  range of `gnsCoe`.
* `Analysis/CStarHilbertCountableBasis` Gram--Schmidts that sequence into a
  Hilbert basis indexed by a subtype of `ℕ`, so `HilbertBasis.repr` presents the
  sum as `ℓ²` over a small index, and `separableSpace_of_hilbertBasis` makes it
  separable.
* `Analysis/CStarHilbertTransport` conjugates the representation along that
  isometry.

## Why the spectral order does not appear

The canonical map of the algebra into a GNS space is taken here to be
`a ↦ π_φ(a)Ω` rather than the coercion of the pre-GNS space into its completion.
The two agree --- that is `CStarTensor.gnsRep_apply_gnsVector` --- and the first
form mentions neither `State.toPositive` nor the spectral order that
`PositiveLinearMap` is stated over, so none of those order instances have to be
reinstalled here.  Density of the range is then
`CStarTensor.dense_range_gnsRep_gnsVector`, and continuity is contractivity of
the GNS representation together with `‖Ω‖ = 1`.
-/

namespace GroupApproximation
namespace CStarState

open InnerProductSpace

open scoped InnerProductSpace

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

/-! ## The algebra inside a GNS space -/

/-- The canonical map of the algebra into the GNS space of a state, written
through the representation: `a ↦ π_φ(a)Ω`.  By
`CStarTensor.gnsRep_apply_gnsVector` this is the canonical image `a ↦ [a]` of
the pre-GNS space, which is what makes its range dense. -/
def gnsCoe (φ : State A) (a : A) : φ.GNSSpace :=
  (φ.gnsRep).hom a φ.gnsVector

theorem gnsCoe_apply (φ : State A) (a : A) :
    gnsCoe φ a = (φ.gnsRep).hom a φ.gnsVector := rfl

/-- **The canonical map is a contraction.**  The GNS representation is
contractive and the cyclic vector is a unit vector. -/
theorem norm_gnsCoe_le (φ : State A) (a : A) : ‖gnsCoe φ a‖ ≤ ‖a‖ := by
  have h1 : ‖gnsCoe φ a‖ ≤ ‖(φ.gnsRep).hom a‖ * ‖φ.gnsVector‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [φ.norm_gnsVector, mul_one] at h1
  exact h1.trans (φ.norm_gnsRep_apply_le a)

/-- `gnsCoe` is continuous: it is linear and contractive. -/
theorem continuous_gnsCoe (φ : State A) : Continuous (gnsCoe φ) := by
  refine (LipschitzWith.mk_one fun a b ↦ ?_).continuous
  have hsub : gnsCoe φ a - gnsCoe φ b = gnsCoe φ (a - b) := by
    simp only [gnsCoe_apply, map_sub, sub_apply]
  rw [dist_eq_norm, dist_eq_norm, hsub]
  exact norm_gnsCoe_le φ (a - b)

/-- **The algebra is dense in its GNS space**, in the form the descent needs it:
the orbit of the cyclic vector is the canonical image of the algebra, so this is
`CStarTensor.dense_range_gnsRep_gnsVector`. -/
theorem denseRange_gnsCoe (φ : State A) : DenseRange (gnsCoe φ) :=
  CStarTensor.dense_range_gnsRep_gnsVector φ

/-- **A vector orthogonal to the image of a dense subset is zero.**  Two
applications of `Continuous.ext_on`: first along the dense subset of the
algebra, then along the dense range of `gnsCoe`. -/
theorem eq_zero_of_forall_inner_gnsCoe_eq_zero (φ : State A) {s : Set A}
    (hs : Dense s) {y : φ.GNSSpace}
    (h : ∀ a ∈ s, ⟪gnsCoe φ a, y⟫_ℂ = 0) : y = 0 := by
  have hall : ∀ a : A, ⟪gnsCoe φ a, y⟫_ℂ = 0 := by
    have hcont : Continuous fun a : A ↦ ⟪gnsCoe φ a, y⟫_ℂ :=
      (continuous_inner.comp ((continuous_gnsCoe φ).prodMk continuous_const))
    have := Continuous.ext_on hs hcont continuous_const h
    exact fun a ↦ congrFun this a
  have hz : ∀ z : φ.GNSSpace, ⟪z, y⟫_ℂ = 0 := by
    have hcont : Continuous fun z : φ.GNSSpace ↦ ⟪z, y⟫_ℂ :=
      continuous_inner.comp (continuous_id.prodMk continuous_const)
    have := Continuous.ext_on (denseRange_gnsCoe φ) hcont continuous_const
      (by rintro _ ⟨a, rfl⟩; exact hall a)
    exact fun z ↦ congrFun this z
  exact inner_self_eq_zero.mp (hz y)

/-! ## The descent -/

section Descent

variable [TopologicalSpace.SeparableSpace A]

/-- **A separable C-star algebra acts faithfully on a separable Hilbert space in
`Type 0`.**  The algebra may live in any universe; the space does not.

The Hilbert space produced is `ℓ²` over a subtype of `ℕ`, obtained by
Gram--Schmidt from the countable family `lp.single n (gnsCoe (ψ n) b)` inside
the GNS sum, and the representation is the diagonal GNS action conjugated along
the resulting isometry. -/
theorem exists_typeZero_faithful_representation :
    ∃ (H : Type) (hgroup : NormedAddCommGroup H),
      letI : NormedAddCommGroup H := hgroup
      ∃ hinner : InnerProductSpace ℂ H,
        letI : InnerProductSpace ℂ H := hinner
        ∃ (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
          (_ : ¬ FiniteDimensional ℂ H)
          (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)), Function.Injective π := by
  classical
  -- A countable separating family of states, reindexed by `ℕ`.
  obtain ⟨s, hs_count, ψ, hsep⟩ := exists_countable_separating_states (A := A)
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
  obtain ⟨i₀, -⟩ := hsep a₀ ha₀
  obtain ⟨g, hg⟩ := hs_count.exists_eq_range ⟨i₀.1, i₀.2⟩
  have hgmem : ∀ n, g n ∈ s := fun n ↦ by rw [hg]; exact ⟨n, rfl⟩
  set ψ' : ℕ → State A := fun n ↦ ψ ⟨g n, hgmem n⟩
  have hsep' : ∀ a : A, a ≠ 0 → ∃ n, ((ψ' n).gnsRep).hom a ≠ 0 := by
    intro a ha
    obtain ⟨i, hi⟩ := hsep a ha
    have hmem : (i : A) ∈ Set.range g := by rw [← hg]; exact i.2
    obtain ⟨n, hn⟩ := hmem
    refine ⟨n, ?_⟩
    have hstate : ψ' n = ψ i := congrArg ψ (Subtype.ext hn)
    rw [hstate]
    exact hi
  -- A countable dense subset of the algebra, reindexed by `ℕ`.
  obtain ⟨t, ht_count, ht_dense⟩ := TopologicalSpace.exists_countable_dense A
  obtain ⟨tf, htf⟩ := ht_count.exists_eq_range ht_dense.nonempty
  have htf_dense : Dense (Set.range tf) := by rw [← htf]; exact ht_dense
  -- The countable family inside the GNS sum, and its totality.
  set F : ℕ → FamilyGNSSpace ψ' := fun k ↦
    lp.single 2 (Nat.pairEquiv.symm k).1
      (gnsCoe (ψ' (Nat.pairEquiv.symm k).1) (tf (Nat.pairEquiv.symm k).2))
    with hF
  have hFpair : ∀ n m : ℕ,
      F (Nat.pairEquiv (n, m)) = lp.single 2 n (gnsCoe (ψ' n) (tf m)) := by
    intro n m
    have h : Nat.pairEquiv.symm (Nat.pairEquiv (n, m)) = (n, m) :=
      Equiv.symm_apply_apply _ _
    show (fun p : ℕ × ℕ ↦ (lp.single 2 p.1 (gnsCoe (ψ' p.1) (tf p.2)) : FamilyGNSSpace ψ'))
        (Nat.pairEquiv.symm (Nat.pairEquiv (n, m)))
      = (fun p : ℕ × ℕ ↦ (lp.single 2 p.1 (gnsCoe (ψ' p.1) (tf p.2)) : FamilyGNSSpace ψ')) (n, m)
    exact congrArg
      (fun p : ℕ × ℕ ↦ (lp.single 2 p.1 (gnsCoe (ψ' p.1) (tf p.2)) : FamilyGNSSpace ψ')) h
  have hFtotal : (Submodule.span ℂ (Set.range F))ᗮ = ⊥ := by
    refine CStarHilbertCountableBasis.orthogonal_span_eq_bot_of_forall F ?_
    intro x hx
    have hcoord : ∀ n : ℕ, (x : ∀ i : ℕ, (ψ' i).GNSSpace) n = 0 := by
      intro n
      refine eq_zero_of_forall_inner_gnsCoe_eq_zero (ψ' n) htf_dense ?_
      rintro _ ⟨m, rfl⟩
      have hk := hx (Nat.pairEquiv (n, m))
      rw [hFpair n m, lp.inner_single_left] at hk
      exact hk
    refine lp.ext (funext fun n ↦ ?_)
    simpa using hcoord n
  -- Gram--Schmidt down to a small index, and the transport.
  set b := CStarHilbertCountableBasis.countableGramSchmidtBasis F hFtotal
  refine ⟨lp (fun _ : {i : ℕ | gramSchmidtNormed ℂ F i ≠ 0} ↦ ℂ) 2,
    inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact CStarHilbertCountableBasis.separableSpace_of_hilbertBasis
      (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _))
  · -- The sum carries an orthonormal sequence, and `b.repr` is an isometry, so
    -- the clause transports.  `Theorem4TailPairStatement` asks for it because
    -- the printed models cannot be placed on a finite-dimensional space.
    intro hfd
    haveI := hfd
    exact not_finiteDimensional_familyGNSSpace ψ'
      (LinearEquiv.finiteDimensional b.repr.symm.toLinearEquiv)
  · exact ⟨(CStarHilbertTransport.conjStarAlgHom b.repr).comp
      (familyGNSStarAlgHom ψ'),
      CStarHilbertTransport.injective_comp_conjStarAlgHom b.repr
        (familyGNSStarAlgHom ψ') (familyGNSStarAlgHom_injective ψ' hsep')⟩

end Descent

/-! ## The recognition route's last cited input, discharged -/

/-- **`ShulmanFill.SeparableFaithfulRepresentationStatement` is a theorem.**  It
is the hypothesis `conjugateWordNorming_of_printedPair_of_compatible'` below
discharges, which leaves `Theorem4PrintedPairStatement` and
`CompatibleTargetPairStatement` --- the two the manuscript itself cites.

That reading is no longer available: `Theorem4PrintedPairStatement` is refuted
by `Analysis/ShulmanFillNormingPrintedPairRefuted` and
`Analysis/ShulmanFillNormingPrintedPairCharacter`, so this theorem is a true
implication out of a false hypothesis and establishes nothing about
`ConjugateWordNormingStatement`.  The statement to quote is
`ShulmanFill.conjugateWordNorming_of_tailPair_of_compatible`
(`Analysis/ShulmanFillNormingTailRoute`), which is this theorem on the repaired
binder.  This one is kept because it is what the refutation is about. -/
theorem separableFaithfulRepresentation :
    ShulmanFill.SeparableFaithfulRepresentationStatement.{u} := by
  intro B _ _ _
  obtain ⟨H, hgroup, hinner, hcomplete, hsep, _hfd, π, hπ⟩ :=
    exists_typeZero_faithful_representation (A := B)
  exact ⟨H, hgroup, hinner, hcomplete, hsep, π, hπ⟩

end

end CStarState

/-! ## The recognition route, with two hypotheses instead of three -/

namespace ShulmanFill

/-- **The recognition statement from the two Props the manuscript cites.**

`conjugateWordNorming_of_printedPair_of_compatible` carries a third hypothesis,
`SeparableFaithfulRepresentationStatement`, because Gelfand--Naimark on a
separable Hilbert space was neither in the tree nor in Mathlib at the pinned
revision.  `CStarState.separableFaithfulRepresentation` proves it, so the third
hypothesis can be discharged where it stands, leaving Shulman's Theorem 4 in its
printed-pair form and his Theorem 13 in its compatible-target-pair form.

The universe is pinned at `1` because the algebra the representation is built
for is the symmetric double `D *_C D`, which lies one universe above `C` and `D`
while its Hilbert space has to stay in `Type 0`. -/
theorem conjugateWordNorming_of_printedPair_of_compatible'
    [∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)]
    (hT4 : Theorem4PrintedPairStatement)
    (hCTP : ShulmanSymmetricDouble.CompatibleTargetPairStatement) :
    ConjugateWordNormingStatement :=
  conjugateWordNorming_of_printedPair_of_compatible hT4 hCTP
    CStarState.separableFaithfulRepresentation.{1}

end ShulmanFill
end GroupApproximation
