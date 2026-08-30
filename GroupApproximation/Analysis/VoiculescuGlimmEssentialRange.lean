import GroupApproximation.Analysis.VoiculescuGlimmSelection

/-!
# (V2) The joint essential numerical range, and why it is convex

The separation puts the state's tuple of values in the closed convex hull of
the vector-state tuples off one finite-dimensional subspace.  To get a single
vector out of that, the convex hull has to be removed, and this module is where
that happens: it introduces the set of tuples that are approximable off
**every** finite-dimensional subspace at once, and proves that set convex.

    `vectorStateTuples a V = {(re ⟪aᵢ ξ, ξ⟫)ᵢ : ‖ξ‖ = 1, ξ ∈ Vᗮ}`
    `essentialRange a = ⋂ V finite-dimensional, closure (vectorStateTuples a V)`

`essentialRange` is the joint essential numerical range of the family, and its
convexity is the classical theorem this module proves.  Being an intersection
of closed sets it is closed for free, so once it is known convex it satisfies
`closure (convexHull ℝ (essentialRange a)) = essentialRange a` — which is what
lets the next module separate against it and land back inside a genuine
`closure (vectorStateTuples a V)`, that is, at a genuine unit vector off `V`.

## Only the two-vector case is proved here

Convexity is a statement about a combination of two points, and `convexHull_min`
extends it to combinations of any length for free.  So a successive selection
over `m` vectors is never needed: given `z, z'` in the range and a target `V`,
pick `ξ₁` off `V` realizing `z`, enlarge to
`selectionObstruction a V ξ₁ = V ⊔ span {ξ₁, a₁ξ₁, …}`, pick `ξ₂` off *that*
realizing `z'`, and superpose with the coefficients `√s, √t`.  The result is a
unit vector off `V`, and both orders of cross term vanish exactly — the first
because `aᵢ ξ₁` lies in the enlarged subspace, the second by self-adjointness.
That is `exists_unit_orthogonal_pair_value`, and the rest is bookkeeping.

## The model test

Take `H = ℓ²` and one operator `a =` the rank-one projection onto `e₀`.  Then
`vectorStateTuples a V` is the set of `|⟪ξ, e₀⟫|²` over unit `ξ ∈ Vᗮ`, which is
`{0}` as soon as `e₀ ∈ V`, and `0` lies in the closure for every `V` because a
unit vector of `(V ⊔ span {e₀})ᗮ` gives the value on the nose.  So the range is
`{0}` — the tail value, and the value a state killing the compacts must take.
Convexity is not vacuous there: for `a₁ = diag(1,0,1,0,…)` and `a₂ = 1 - a₁`
the range is the whole segment from `(1,0)` to `(0,1)`, and the interior points
of that segment are reached only through the superposition built below.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The quadratic form of an operator at a real superposition of two vectors
whose cross terms vanish.  This is the two-term case of
`inner_sum_smul_of_inner_eq_zero`, stated without the `Fin 2` vector-notation
layer because two terms is all the convexity argument ever needs. -/
theorem inner_pair_smul_of_inner_eq_zero (c₁ c₂ : ℝ) (x y : H) (b : H →L[ℂ] H)
    (h₁ : ⟪b x, y⟫_ℂ = 0) (h₂ : ⟪b y, x⟫_ℂ = 0) :
    ⟪b ((c₁ : ℂ) • x + (c₂ : ℂ) • y), (c₁ : ℂ) • x + (c₂ : ℂ) • y⟫_ℂ
      = ((c₁ * c₁ : ℝ) : ℂ) * ⟪b x, x⟫_ℂ + ((c₂ * c₂ : ℝ) : ℂ) * ⟪b y, y⟫_ℂ := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, h₁, h₂, mul_zero, add_zero, zero_add]
  push_cast
  ring

omit [CompleteSpace H] in
/-- The squared norm of a superposition of two orthogonal vectors, as the same
identity at the identity operator. -/
theorem inner_self_pair_smul_of_inner_eq_zero (c₁ c₂ : ℝ) (x y : H)
    (h : ⟪x, y⟫_ℂ = 0) :
    ⟪(c₁ : ℂ) • x + (c₂ : ℂ) • y, (c₁ : ℂ) • x + (c₂ : ℂ) • y⟫_ℂ
      = ((c₁ * c₁ : ℝ) : ℂ) * ⟪x, x⟫_ℂ + ((c₂ * c₂ : ℝ) : ℂ) * ⟪y, y⟫_ℂ :=
  inner_pair_smul_of_inner_eq_zero c₁ c₂ x y 1 h (inner_eq_zero_symm.mp h)

/-- The tuples of values of a family at unit vectors orthogonal to `V`.  This is
the set the separation puts the state's values in the closed convex hull of. -/
def vectorStateTuples {n : ℕ} (a : Fin n → (H →L[ℂ] H)) (V : Submodule ℂ H) :
    Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | ∃ ξ : H, ξ ∈ Vᗮ ∧ ‖ξ‖ = 1 ∧ ∀ i, x i = (⟪a i ξ, ξ⟫_ℂ).re}

omit [CompleteSpace H] in
theorem mem_vectorStateTuples_iff {n : ℕ} (a : Fin n → (H →L[ℂ] H))
    (V : Submodule ℂ H) (x : Fin n → ℝ) :
    x ∈ vectorStateTuples a V ↔
      ∃ ξ : H, ξ ∈ Vᗮ ∧ ‖ξ‖ = 1 ∧ ∀ i, x i = (⟪a i ξ, ξ⟫_ℂ).re :=
  Iff.rfl

/-- **The joint essential numerical range.**  The tuples approximable by vector
states off every finite-dimensional subspace at once. -/
def essentialRange {n : ℕ} (a : Fin n → (H →L[ℂ] H)) : Set (Fin n → ℝ) :=
  ⋂ V : {W : Submodule ℂ H // FiniteDimensional ℂ W},
    closure (vectorStateTuples a V.1)

omit [CompleteSpace H] in
theorem mem_essentialRange_iff {n : ℕ} (a : Fin n → (H →L[ℂ] H)) (x : Fin n → ℝ) :
    x ∈ essentialRange a ↔
      ∀ V : Submodule ℂ H, FiniteDimensional ℂ V →
        x ∈ closure (vectorStateTuples a V) := by
  constructor
  · intro hx V hV
    exact Set.mem_iInter.mp hx ⟨V, hV⟩
  · intro h
    exact Set.mem_iInter.mpr fun V ↦ h V.1 V.2

omit [CompleteSpace H] in
theorem isClosed_essentialRange {n : ℕ} (a : Fin n → (H →L[ℂ] H)) :
    IsClosed (essentialRange a) :=
  isClosed_iInter fun _ ↦ isClosed_closure

omit [CompleteSpace H] in
/-- Enlarging the subspace shrinks the set of tuples: a unit vector orthogonal
to the bigger space is orthogonal to the smaller one. -/
theorem vectorStateTuples_subset_of_le {n : ℕ} (a : Fin n → (H →L[ℂ] H))
    {V W : Submodule ℂ H} (h : V ≤ W) :
    vectorStateTuples a W ⊆ vectorStateTuples a V := by
  intro x hx
  obtain ⟨ξ, hξ, hnorm, hval⟩ := (mem_vectorStateTuples_iff a W x).mp hx
  exact (mem_vectorStateTuples_iff a V x).mpr
    ⟨ξ, Submodule.orthogonal_le h hξ, hnorm, hval⟩

omit [CompleteSpace H] in
/-- The tuples are bounded by the norms of the operators. -/
theorem vectorStateTuples_subset_closedBall {n : ℕ} (a : Fin n → (H →L[ℂ] H))
    (V : Submodule ℂ H) :
    vectorStateTuples a V ⊆ Metric.closedBall 0 (∑ i, ‖a i‖) := by
  have hR : (0 : ℝ) ≤ ∑ i, ‖a i‖ := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  intro x hx
  obtain ⟨ξ, -, hnorm, hval⟩ := (mem_vectorStateTuples_iff a V x).mp hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro i
  have hbound : |x i| ≤ ‖a i‖ := by
    rw [hval i]
    calc |(⟪a i ξ, ξ⟫_ℂ).re|
        ≤ ‖⟪a i ξ, ξ⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖a i ξ‖ * ‖ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖a i‖ * ‖ξ‖ * ‖ξ‖ :=
          mul_le_mul_of_nonneg_right ((a i).le_opNorm ξ) (norm_nonneg _)
      _ = ‖a i‖ := by rw [hnorm, mul_one, mul_one]
  have hsingle : ‖a i‖ ≤ ∑ j, ‖a j‖ :=
    Finset.single_le_sum (f := fun j ↦ ‖a j‖) (fun j _ ↦ norm_nonneg _)
      (Finset.mem_univ i)
  rw [Pi.zero_apply, Real.dist_eq, sub_zero]
  exact hbound.trans hsingle

omit [CompleteSpace H] in
theorem isCompact_closure_vectorStateTuples {n : ℕ} (a : Fin n → (H →L[ℂ] H))
    (V : Submodule ℂ H) : IsCompact (closure (vectorStateTuples a V)) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure
    ((Metric.isBounded_closedBall.subset
      (vectorStateTuples_subset_closedBall a V)).closure)

omit [CompleteSpace H] in
/-- On an infinite-dimensional space there is always a unit vector off a
finite-dimensional subspace, so the tuples are never absent. -/
theorem vectorStateTuples_nonempty {n : ℕ} (a : Fin n → (H →L[ℂ] H))
    (hH : ¬ FiniteDimensional ℂ H) (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    (vectorStateTuples a V).Nonempty := by
  have htop : ¬ FiniteDimensional ℂ (⊤ : Submodule ℂ H) := by
    intro hfin
    exact hH (Submodule.topEquiv.finiteDimensional)
  obtain ⟨ξ, -, hξV, hξnorm⟩ :=
    exists_norm_eq_one_mem_orthogonal (W := (⊤ : Submodule ℂ H)) (V := V) htop
  exact ⟨fun i ↦ (⟪a i ξ, ξ⟫_ℂ).re,
    (mem_vectorStateTuples_iff a V _).mpr ⟨ξ, hξV, hξnorm, fun i ↦ rfl⟩⟩

/-- **The two-vector selection.**  A unit vector orthogonal to `V` whose values
are the prescribed convex combination of the values at `ξ₁` and at `ξ₂`,
exactly — not approximately.  The second vector is taken orthogonal to the
obstruction subspace built from the first, which kills `⟪aᵢ ξ₁, ξ₂⟫`; the
reverse cross term `⟪aᵢ ξ₂, ξ₁⟫` is then killed by self-adjointness. -/
theorem exists_unit_orthogonal_pair_value {n : ℕ} (a : Fin n → (H →L[ℂ] H))
    (hsa : ∀ i, IsSelfAdjoint (a i)) (V : Submodule ℂ H)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    {ξ₁ ξ₂ : H} (hξ₁V : ξ₁ ∈ Vᗮ) (hξ₁ : ‖ξ₁‖ = 1)
    (hξ₂X : ξ₂ ∈ (selectionObstruction a V ξ₁)ᗮ) (hξ₂ : ‖ξ₂‖ = 1) :
    ∃ ζ : H, ζ ∈ Vᗮ ∧ ‖ζ‖ = 1 ∧
      ∀ i, (⟪a i ζ, ζ⟫_ℂ).re
        = s * (⟪a i ξ₁, ξ₁⟫_ℂ).re + t * (⟪a i ξ₂, ξ₂⟫_ℂ).re := by
  have hperp : ⟪ξ₁, ξ₂⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp hξ₂X ξ₁ (mem_selectionObstruction a V ξ₁)
  have haperp : ∀ i, ⟪a i ξ₁, ξ₂⟫_ℂ = 0 := fun i ↦
    (Submodule.mem_orthogonal _ _).mp hξ₂X (a i ξ₁)
      (apply_mem_selectionObstruction a V ξ₁ i)
  have haperp' : ∀ i, ⟪a i ξ₂, ξ₁⟫_ℂ = 0 := by
    intro i
    have hswap : ⟪a i ξ₂, ξ₁⟫_ℂ = ⟪ξ₂, a i ξ₁⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left,
        ← ContinuousLinearMap.star_eq_adjoint, (hsa i).star_eq]
    rw [hswap, inner_eq_zero_symm]
    exact haperp i
  have hcc₁ : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs
  have hcc₂ : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht
  have hone₁ : ⟪ξ₁, ξ₁⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hξ₁]
    norm_num
  have hone₂ : ⟪ξ₂, ξ₂⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hξ₂]
    norm_num
  refine ⟨(Real.sqrt s : ℂ) • ξ₁ + (Real.sqrt t : ℂ) • ξ₂, ?_, ?_, ?_⟩
  · exact Vᗮ.add_mem (Vᗮ.smul_mem _ hξ₁V)
      (Vᗮ.smul_mem _
        (Submodule.orthogonal_le (le_selectionObstruction a V ξ₁) hξ₂X))
  · have hself : ⟪(Real.sqrt s : ℂ) • ξ₁ + (Real.sqrt t : ℂ) • ξ₂,
        (Real.sqrt s : ℂ) • ξ₁ + (Real.sqrt t : ℂ) • ξ₂⟫_ℂ = 1 := by
      rw [inner_self_pair_smul_of_inner_eq_zero _ _ _ _ hperp, hone₁, hone₂,
        mul_one, mul_one, hcc₁, hcc₂, ← Complex.ofReal_add, hst, Complex.ofReal_one]
    have hsq : ‖(Real.sqrt s : ℂ) • ξ₁ + (Real.sqrt t : ℂ) • ξ₂‖ ^ 2 = 1 := by
      have h2 : ⟪(Real.sqrt s : ℂ) • ξ₁ + (Real.sqrt t : ℂ) • ξ₂,
          (Real.sqrt s : ℂ) • ξ₁ + (Real.sqrt t : ℂ) • ξ₂⟫_ℂ
            = ((‖(Real.sqrt s : ℂ) • ξ₁ + (Real.sqrt t : ℂ) • ξ₂‖ : ℝ) : ℂ) ^ 2 :=
        inner_self_eq_norm_sq_to_K _
      rw [hself] at h2
      exact_mod_cast h2.symm
    rw [← Real.sqrt_sq
        (norm_nonneg ((Real.sqrt s : ℂ) • ξ₁ + (Real.sqrt t : ℂ) • ξ₂)),
      hsq, Real.sqrt_one]
  · intro i
    rw [inner_pair_smul_of_inner_eq_zero _ _ _ _ _ (haperp i) (haperp' i), hcc₁,
      hcc₂, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

/-- **Convexity of the joint essential numerical range.**  This is the step an
`m`-fold successive selection would otherwise be needed for: `convexHull_min`
turns the two-vector case into combinations of every length. -/
theorem convex_essentialRange {n : ℕ} (a : Fin n → (H →L[ℂ] H))
    (hsa : ∀ i, IsSelfAdjoint (a i)) : Convex ℝ (essentialRange a) := by
  intro z hz z' hz' s t hs ht hst
  rw [mem_essentialRange_iff] at hz hz' ⊢
  intro V hV
  haveI : FiniteDimensional ℂ V := hV
  rw [Metric.mem_closure_iff]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := half_pos hδ
  obtain ⟨x₁, hx₁mem, hx₁⟩ := Metric.mem_closure_iff.mp (hz V hV) (δ / 2) hδ2
  obtain ⟨ξ₁, hξ₁V, hξ₁norm, hξ₁val⟩ := (mem_vectorStateTuples_iff a V x₁).mp hx₁mem
  obtain ⟨x₂, hx₂mem, hx₂⟩ :=
    Metric.mem_closure_iff.mp
      (hz' (selectionObstruction a V ξ₁) inferInstance) (δ / 2) hδ2
  obtain ⟨ξ₂, hξ₂X, hξ₂norm, hξ₂val⟩ :=
    (mem_vectorStateTuples_iff a (selectionObstruction a V ξ₁) x₂).mp hx₂mem
  obtain ⟨ζ, hζV, hζnorm, hζval⟩ :=
    exists_unit_orthogonal_pair_value a hsa V hs ht hst hξ₁V hξ₁norm hξ₂X hξ₂norm
  refine ⟨fun i ↦ (⟪a i ζ, ζ⟫_ℂ).re,
    (mem_vectorStateTuples_iff a V _).mpr ⟨ζ, hζV, hζnorm, fun i ↦ rfl⟩, ?_⟩
  rw [dist_pi_lt_iff hδ]
  intro i
  have h₁ : |z i - x₁ i| ≤ δ / 2 := by
    have hd := (dist_pi_lt_iff hδ2).mp hx₁ i
    rw [Real.dist_eq] at hd
    exact hd.le
  have h₂ : |z' i - x₂ i| ≤ δ / 2 := by
    have hd := (dist_pi_lt_iff hδ2).mp hx₂ i
    rw [Real.dist_eq] at hd
    exact hd.le
  obtain ⟨h₁l, h₁r⟩ := abs_le.mp h₁
  obtain ⟨h₂l, h₂r⟩ := abs_le.mp h₂
  have hb₁ : s * (z i - x₁ i) ≤ s * (δ / 2) := mul_le_mul_of_nonneg_left h₁r hs
  have hb₂ : t * (z' i - x₂ i) ≤ t * (δ / 2) := mul_le_mul_of_nonneg_left h₂r ht
  have hb₃ : s * (-(δ / 2)) ≤ s * (z i - x₁ i) := mul_le_mul_of_nonneg_left h₁l hs
  have hb₄ : t * (-(δ / 2)) ≤ t * (z' i - x₂ i) := mul_le_mul_of_nonneg_left h₂l ht
  have hsum : s * (δ / 2) + t * (δ / 2) = δ / 2 := by rw [← add_mul, hst, one_mul]
  have hsum' : s * (-(δ / 2)) + t * (-(δ / 2)) = -(δ / 2) := by
    rw [← add_mul, hst, one_mul]
  have hexp : (s • z + t • z') i - (⟪a i ζ, ζ⟫_ℂ).re
      = s * (z i - x₁ i) + t * (z' i - x₂ i) := by
    rw [hζval i, hξ₁val i, hξ₂val i]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  show dist ((s • z + t • z') i) ((⟪a i ζ, ζ⟫_ℂ).re) < δ
  rw [Real.dist_eq, hexp, abs_lt]
  constructor
  · linarith
  · linarith

end

end ShulmanFill
end GroupApproximation
