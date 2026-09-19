import GroupApproximation.Kazhdan.KazhdanDisplacementCriterion

/-!
# Property `(T)` is a uniform norm gap for the orbit average

`Kazhdan/Kazhdan.lean` defines property `(T)` by quantifying over *all*
orthogonal representations with an almost invariant unit vector.  That shape is
the right definition and the wrong interface: nothing about a group can be
checked against it directly, which is why every route to `(T)` in this
repository so far has been a citation.

This module replaces the quantifier by a **norm inequality for one explicit
operator**.  For a finite set `S ⊆ G` the orbit average

```
    A_S x = |S|⁻¹ • ∑_{q ∈ S} ρ(q) x
```

is a finite linear combination of the representation's own operators.
`OrbitAverageGap G S lam` says that `‖A_S‖ ≤ lam` in every representation with
no nonzero invariant vector, uniformly.  The two theorems below are converse to
each other:

* `isKazhdanPair_of_orbitAverageGap` --- a gap `lam < 1` **is** a Kazhdan pair,
  at the explicit tolerance `1 - lam`; and
* `orbitAverageGap_of_isKazhdanPair` --- a Kazhdan pair `(Q, ε)` gives the gap
  `1 - ε²/(4|S|)` for any finite `S ⊇ Q` containing the identity.

`hasKazhdanPropertyT_iff_exists_orbitAverageGap` is the resulting equivalence:
a group has property `(T)` exactly when some finite subset has an orbit average
that is a uniform strict contraction off the invariant vectors.  Neither
direction is assumed: both are proved here, from the definitions.

`weightedAverage` and `WeightedAverageGap` carry the same criterion for a convex
combination `∑_{q ∈ S} w q • ρ(q) x` rather than a uniform one, because the
operator that Garland's method actually bounds is the Laplacian of a weighted
graph.  `isKazhdanPair_of_weightedAverageGap` is that version, at tolerance
`(1 - lam)/2`, and `weightedAverage_const` checks that the uniform statement is
its constant-weight case.  `Kazhdan/OrbitAverageFormGap.lean` goes one step
further and asks only for a bound on the Rayleigh quotient `⟪A x, x⟫ / ‖x‖²`,
which is what an eigenvalue estimate actually gives; that version needs no
self-adjointness, and it subsumes the norm versions here.

## Why this is the interface the literature's `(T)` proofs actually produce

Every unconditional proof of `(T)` for an infinite group known to the author of
this module ends at a spectral estimate of exactly this shape, not at the
almost-invariant-vector definition:

* Garland's method, and its combinatorial descendants --- Ballmann and
  Świątkowski, *On `L²`-cohomology and property `(T)` for automorphism groups of
  polyhedral cell complexes*, and Żuk, *La propriété `(T)` de Kazhdan pour les
  groupes agissant sur les polyèdres* --- bound the Laplacian of a group acting
  on a simply connected complex by the smallest positive eigenvalue of the
  finite link graphs.  The output is an operator norm bound on an average, which
  is `OrbitAverageGap`;
* the spectral criterion of Ershov and Jaikin-Zapirain, *Property `(T)` for
  noncommutative universal lattices*, bounds a sum of projections onto the fixed
  spaces of finite subgroups, again an operator estimate;
* Kostant's theorem for `Sp(n,1)`, used by the lattice route of
  `Kazhdan/SharpExistenceRoutes.lean`, is a statement about the unitary dual and
  reaches the group only through such an estimate.

So the equivalence below is the seam at which any of those arguments would be
attached: a formalization of Żuk's criterion would produce
`OrbitAverageGap G S lam` and nothing else, and
`isKazhdanPair_of_orbitAverageGap` is the step from there to
`HasKazhdanPropertyT` that is now machine-checked rather than quoted.

## What this module does not do

It supplies no gap.  `orbitAverageGap_of_isKazhdanPair` is the only source of a
gap here, and it consumes a Kazhdan pair, so no infinite group acquires
property `(T)` from this file.  The honest statement of that is
`hasKazhdanPropertyT_iff_exists_orbitAverageGap` itself: because the criterion
is an *equivalence*, it is a change of interface and not a reduction, and
`Kazhdan/SharpExistenceSpectralRoute.lean` records what that means for
`SharpExistence`.  `Kazhdan/OrbitAverageFiniteControl.lean` carries the positive
control --- a finite group has gap constant `0` --- in a separate module, so
that the criterion proved here does not depend on it.
-/

namespace GroupApproximation
namespace SpectralGap

universe u v

/-- **A uniform norm gap for the orbit average over `S`.**  In every complete
orthogonal representation of `G` with no nonzero invariant vector, the average
of the orbit of any vector over the finite set `S` is shorter than the vector by
the factor `lam`.

The quantifier over representations is the same one that appears in
`IsKazhdanPair`, so the two statements live at the same universe level and no
universe-independence claim is implicit in the comparison below. -/
def OrbitAverageGap (G : Type u) [Group G] (S : Finset G) (lam : ℝ) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E],
    ∀ ρ : G →* (E ≃ₗᵢ[ℝ] E), IsKazhdanPair.HasNoInvariantVectors G ρ →
      ∀ x : E, ‖IsKazhdanPair.orbitAverage S ρ x‖ ≤ lam * ‖x‖

/-- **A weighted orbit average.**  The convex combination `∑_{q ∈ S} w q • ρ(q) x`
of the orbit of `x`.  `IsKazhdanPair.orbitAverage` is the case of constant
weights `|S|⁻¹`; the extra generality is not decoration, because the operator a
Garland-type argument bounds is the Laplacian of a weighted graph, whose weights
are link degrees and are not constant. -/
noncomputable def weightedAverage {G : Type u} [Group G] {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (S : Finset G) (w : G → ℝ)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : E :=
  ∑ q ∈ S, w q • ρ q x

/-- **A uniform norm gap for a weighted orbit average**, the weighted form of
`OrbitAverageGap`. -/
def WeightedAverageGap (G : Type u) [Group G] (S : Finset G) (w : G → ℝ)
    (lam : ℝ) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E],
    ∀ ρ : G →* (E ≃ₗᵢ[ℝ] E), IsKazhdanPair.HasNoInvariantVectors G ρ →
      ∀ x : E, ‖weightedAverage S w ρ x‖ ≤ lam * ‖x‖

variable {G : Type u} [Group G]

/-- A gap only weakens as its constant grows. -/
theorem OrbitAverageGap.mono {S : Finset G} {lam lam' : ℝ} (hlam : lam ≤ lam')
    (h : OrbitAverageGap.{u, v} G S lam) : OrbitAverageGap.{u, v} G S lam' := by
  intro E _ _ _ ρ hno x
  refine (h E ρ hno x).trans ?_
  exact mul_le_mul_of_nonneg_right hlam (norm_nonneg x)

/-! ## The average of a nearly fixed vector is nearly the vector

The only computation in this module: the orbit average is an average, so it
moves a vector by at most the largest displacement of the vectors being
averaged.  The inequality is strict because `S` is nonempty, which is what
allows the tolerance `1 - lam` below to be attained rather than approached. -/

/-- **An orbit average displaces no more than its worst term.**  If every
`q ∈ S` moves `x` by less than `c`, so does the average over `S`. -/
theorem norm_orbitAverage_sub_lt {S : Finset G} (hS : S.Nonempty)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) {c : ℝ}
    (h : ∀ q ∈ S, ‖ρ q x - x‖ < c) :
    ‖IsKazhdanPair.orbitAverage S ρ x - x‖ < c := by
  classical
  have hcardNat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hne : (S.card : ℝ) ≠ 0 := ne_of_gt hcard
  have hrewrite : IsKazhdanPair.orbitAverage S ρ x - x
      = ((S.card : ℝ)⁻¹) • ∑ q ∈ S, (ρ q x - x) := by
    have hxs : (∑ _q ∈ S, x) = (S.card : ℝ) • x := by
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ S.card x]
    rw [IsKazhdanPair.orbitAverage, Finset.sum_sub_distrib, hxs, smul_sub,
      smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hsum : ‖∑ q ∈ S, (ρ q x - x)‖ < (S.card : ℝ) * c := by
    have h1 : ‖∑ q ∈ S, (ρ q x - x)‖ ≤ ∑ q ∈ S, ‖ρ q x - x‖ :=
      norm_sum_le _ _
    have h2 : (∑ q ∈ S, ‖ρ q x - x‖) < ∑ _q ∈ S, c :=
      Finset.sum_lt_sum_of_nonempty hS h
    have h3 : (∑ _q ∈ S, c) = (S.card : ℝ) * c := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  rw [hrewrite, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcard)]
  calc (S.card : ℝ)⁻¹ * ‖∑ q ∈ S, (ρ q x - x)‖
      < (S.card : ℝ)⁻¹ * ((S.card : ℝ) * c) :=
        mul_lt_mul_of_pos_left hsum (inv_pos.mpr hcard)
    _ = c := by rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-! ## The criterion -/

/-- **A uniform orbit-average gap is a Kazhdan pair.**

If the average over `S` contracts by `lam < 1` in every representation without
invariant vectors, then `S` is a Kazhdan set at tolerance `1 - lam`: a unit
vector moved by less than `1 - lam` by every element of `S` is moved by less
than `1 - lam` by the average too, so the average has norm more than `lam`, and
the gap forbids that unless an invariant vector exists.

The tolerance is explicit and optimal for this argument, and no hypothesis
beyond the gap is used --- in particular `S` is not assumed to generate `G`, to
be symmetric, or to contain the identity. -/
theorem isKazhdanPair_of_orbitAverageGap {S : Finset G} (hS : S.Nonempty)
    {lam : ℝ} (hlam : lam < 1) (hgap : OrbitAverageGap.{u, v} G S lam) :
    IsKazhdanPair.{u, v} G S (1 - lam) := by
  have hε : (0 : ℝ) < 1 - lam := by linarith
  refine IsKazhdanPair.of_noInvariant_displacement hε ?_
  intro E _ _ _ ρ hno x hx
  by_contra hcon
  have hnear : ∀ q ∈ S, ‖ρ q x - x‖ < 1 - lam := fun q hq ↦
    lt_of_not_ge (fun hge ↦ hcon ⟨q, hq, hge⟩)
  have hsub : ‖IsKazhdanPair.orbitAverage S ρ x - x‖ < 1 - lam :=
    norm_orbitAverage_sub_lt hS ρ x hnear
  have hgapx : ‖IsKazhdanPair.orbitAverage S ρ x‖ ≤ lam := by
    have hbound := hgap E ρ hno x
    rwa [hx, mul_one] at hbound
  have htri : ‖x‖ ≤ ‖IsKazhdanPair.orbitAverage S ρ x‖ +
      ‖IsKazhdanPair.orbitAverage S ρ x - x‖ := by
    calc ‖x‖
        = ‖IsKazhdanPair.orbitAverage S ρ x -
            (IsKazhdanPair.orbitAverage S ρ x - x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖IsKazhdanPair.orbitAverage S ρ x‖ +
            ‖IsKazhdanPair.orbitAverage S ρ x - x‖ := norm_sub_le _ _
  rw [hx] at htri
  linarith

/-- **A uniform orbit-average gap is property `(T)`.** -/
theorem hasKazhdanPropertyT_of_orbitAverageGap {S : Finset G} (hS : S.Nonempty)
    {lam : ℝ} (hlam : lam < 1) (hgap : OrbitAverageGap.{u, v} G S lam) :
    HasKazhdanPropertyT.{u, v} G :=
  ⟨S, 1 - lam, isKazhdanPair_of_orbitAverageGap hS hlam hgap⟩

/-! ## The weighted form

Żuk's criterion, and Garland's method behind it, bound the norm of a *weighted*
average: the weights are the degrees of the link graph, and they are constant
only when the complex is regular.  The argument above does not use the
uniformity of the weights anywhere, so it survives verbatim, at the cost of one
factor of two in the tolerance --- the weighted displacement estimate is not
strict, because a weight may vanish. -/

/-- **A weighted average displaces no more than its worst term.**  For a convex
combination the estimate is the same as for the uniform average, with the
triangle inequality weighted. -/
theorem norm_weightedAverage_sub_le {S : Finset G} {w : G → ℝ}
    (hw0 : ∀ q ∈ S, 0 ≤ w q) (hw1 : ∑ q ∈ S, w q = 1)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) {c : ℝ}
    (h : ∀ q ∈ S, ‖ρ q x - x‖ ≤ c) :
    ‖weightedAverage S w ρ x - x‖ ≤ c := by
  classical
  have hx : (∑ q ∈ S, w q • x) = x := by
    rw [← Finset.sum_smul, hw1, one_smul]
  have hrw : ∑ q ∈ S, w q • (ρ q x - x) = weightedAverage S w ρ x - x := by
    calc ∑ q ∈ S, w q • (ρ q x - x)
        = (∑ q ∈ S, w q • ρ q x) - ∑ q ∈ S, w q • x := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun q _ ↦ smul_sub (w q) (ρ q x) x
      _ = weightedAverage S w ρ x - x := by rw [hx, weightedAverage]
  rw [← hrw]
  calc ‖∑ q ∈ S, w q • (ρ q x - x)‖
      ≤ ∑ q ∈ S, ‖w q • (ρ q x - x)‖ := norm_sum_le _ _
    _ = ∑ q ∈ S, w q * ‖ρ q x - x‖ := by
        refine Finset.sum_congr rfl fun q hq ↦ ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 q hq)]
    _ ≤ ∑ q ∈ S, w q * c :=
        Finset.sum_le_sum fun q hq ↦
          mul_le_mul_of_nonneg_left (h q hq) (hw0 q hq)
    _ = c := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **A uniform weighted-average gap is a Kazhdan pair.**  The tolerance is
`(1 - lam)/2`: half of the uniform statement's, because the weighted
displacement estimate above is not strict. -/
theorem isKazhdanPair_of_weightedAverageGap {S : Finset G} {w : G → ℝ}
    (hw0 : ∀ q ∈ S, 0 ≤ w q) (hw1 : ∑ q ∈ S, w q = 1)
    {lam : ℝ} (hlam : lam < 1) (hgap : WeightedAverageGap.{u, v} G S w lam) :
    IsKazhdanPair.{u, v} G S ((1 - lam) / 2) := by
  have hε : (0 : ℝ) < (1 - lam) / 2 := by linarith
  refine IsKazhdanPair.of_noInvariant_displacement hε ?_
  intro E _ _ _ ρ hno x hx
  by_contra hcon
  have hnear : ∀ q ∈ S, ‖ρ q x - x‖ ≤ (1 - lam) / 2 := fun q hq ↦
    le_of_lt (lt_of_not_ge (fun hge ↦ hcon ⟨q, hq, hge⟩))
  have hsub : ‖weightedAverage S w ρ x - x‖ ≤ (1 - lam) / 2 :=
    norm_weightedAverage_sub_le hw0 hw1 ρ x hnear
  have hgapx : ‖weightedAverage S w ρ x‖ ≤ lam := by
    have hbound := hgap E ρ hno x
    rwa [hx, mul_one] at hbound
  have htri : ‖x‖ ≤ ‖weightedAverage S w ρ x‖ +
      ‖weightedAverage S w ρ x - x‖ := by
    calc ‖x‖
        = ‖weightedAverage S w ρ x - (weightedAverage S w ρ x - x)‖ := by
          rw [sub_sub_cancel]
      _ ≤ ‖weightedAverage S w ρ x‖ + ‖weightedAverage S w ρ x - x‖ :=
          norm_sub_le _ _
  rw [hx] at htri
  linarith

/-- **A uniform weighted-average gap is property `(T)`.**  This is the statement
a formalization of Żuk's criterion would discharge. -/
theorem hasKazhdanPropertyT_of_weightedAverageGap {S : Finset G} {w : G → ℝ}
    (hw0 : ∀ q ∈ S, 0 ≤ w q) (hw1 : ∑ q ∈ S, w q = 1)
    {lam : ℝ} (hlam : lam < 1) (hgap : WeightedAverageGap.{u, v} G S w lam) :
    HasKazhdanPropertyT.{u, v} G :=
  ⟨S, (1 - lam) / 2, isKazhdanPair_of_weightedAverageGap hw0 hw1 hlam hgap⟩

/-- The uniform average is the weighted average at constant weights, so the
uniform gap is a special case of the weighted one and nothing above is a
separate development. -/
theorem weightedAverage_const {S : Finset G}
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    weightedAverage S (fun _ ↦ ((S.card : ℝ)⁻¹)) ρ x
      = IsKazhdanPair.orbitAverage S ρ x := by
  rw [weightedAverage, IsKazhdanPair.orbitAverage, Finset.smul_sum]

/-! ## The converse, so that the criterion is not lossy -/

/-- **A Kazhdan pair is a uniform orbit-average gap.**  This is
`IsKazhdanPair.norm_orbitAverage_le` read as a statement about the operator
rather than about a single vector: the contraction factor `1 - ε²/(4|S|)` is
the one Kazhdan's argument produces, and it depends on nothing but `ε` and the
size of the alphabet. -/
theorem orbitAverageGap_of_isKazhdanPair {Q S : Finset G} {ε : ℝ}
    (hQ : IsKazhdanPair.{u, v} G Q ε) (hQS : Q ⊆ S) (hone : (1 : G) ∈ S)
    (hεone : ε ≤ 1) :
    OrbitAverageGap.{u, v} G S (1 - ε ^ 2 / (4 * S.card)) := by
  intro E _ _ _ ρ hno x
  exact hQ.norm_orbitAverage_le S hQS hone hεone ρ hno x

/-- **Property `(T)` supplies a uniform orbit-average gap.**  The alphabet is
the Kazhdan set with the identity adjoined, and the tolerance is truncated at
one so that Kazhdan's estimate applies. -/
theorem exists_orbitAverageGap_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{u, v} G) :
    ∃ S : Finset G, ∃ lam : ℝ,
      S.Nonempty ∧ lam < 1 ∧ OrbitAverageGap.{u, v} G S lam := by
  classical
  obtain ⟨Q, ε, hQ⟩ := hT
  refine ⟨insert 1 Q, 1 - (min ε 1) ^ 2 / (4 * (insert (1 : G) Q).card),
    ⟨1, Finset.mem_insert_self 1 Q⟩, ?_, ?_⟩
  · have hSne : (insert (1 : G) Q).Nonempty := ⟨1, Finset.mem_insert_self 1 Q⟩
    have hcard : (0 : ℝ) < (insert (1 : G) Q).card := by
      exact_mod_cast Finset.card_pos.mpr hSne
    have hδpos : 0 < min ε 1 := lt_min hQ.1 zero_lt_one
    have hpos : 0 < (min ε 1) ^ 2 / (4 * (insert (1 : G) Q).card) :=
      div_pos (pow_pos hδpos 2) (by linarith)
    linarith
  · exact orbitAverageGap_of_isKazhdanPair
      (hQ.shrink (lt_min hQ.1 zero_lt_one) (min_le_left _ _))
      (Finset.subset_insert 1 Q) (Finset.mem_insert_self 1 Q)
      (min_le_right _ _)

/-- **Property `(T)` is exactly a uniform orbit-average gap.**

Both directions are proved above, so this is an equivalence of definitions and
not a criterion with a loss.  Read left to right it says every `(T)` group
carries a finite spectral certificate; read right to left it says such a
certificate is enough.  It is the second reading that a formalization of Żuk's
criterion, or of Garland's method, would consume. -/
theorem hasKazhdanPropertyT_iff_exists_orbitAverageGap :
    HasKazhdanPropertyT.{u, v} G ↔
      ∃ S : Finset G, ∃ lam : ℝ,
        S.Nonempty ∧ lam < 1 ∧ OrbitAverageGap.{u, v} G S lam := by
  constructor
  · exact exists_orbitAverageGap_of_hasKazhdanPropertyT
  · rintro ⟨S, lam, hS, hlam, hgap⟩
    exact hasKazhdanPropertyT_of_orbitAverageGap hS hlam hgap

end SpectralGap
end GroupApproximation
