import GroupApproximation.Analysis.CompressionTraceRigidity
import GroupApproximation.Sofic.AmenableActionSofic
import GroupApproximation.Sofic.HyperlinearScalar

/-!
# What Følner buys: the same defect, measured in the other norm

`Analysis.CompressionTraceRigidity` computed the multiplicativity defect of a
compression at the pair `(λ_{g⁻¹}, λ_g)` and found a diagonal projection: the
projection onto the coordinates `g` pushes out of the window.  Its **operator**
norm is therefore `1` unless the window is exactly invariant.

This file measures the same matrix in the normalized Hilbert--Schmidt norm and
finds

```text
    ‖D‖₂²  =  #{q : g · e q ∉ window} / k ,
```

`hsNormSq_inverseDefect` --- an equality, not a bound --- which is exactly the
Følner ratio of the window.  So for an amenable group the very same
compressions are asymptotically multiplicative **in the 2-norm**, to any
prescribed accuracy on any prescribed finite set
(`exists_folner_compression_of_isAmenable`), while their operator-norm defects
sit at `1` (`exists_compression_hsNormSq_lt_and_one_le_norm`).

Read together with `Analysis.CompressionTraceModel` --- where the trace clause
was already an identity and unitality and complete positivity were free --- the
accounting for the printed sentence `INT.11` is complete:

| clause of quasidiagonality | at a Følner compression |
|---|---|
| unital, completely positive | exact, every window |
| normalized trace equals `τ` | exact, every window |
| multiplicative in `‖·‖₂` | asymptotically, by amenability |
| multiplicative in `‖·‖` | **`0` or `1`, never small** |

The whole of Tikuisis--White--Winter, for the application the manuscript makes
of it, is the upgrade of the third line to the fourth --- and this file proves
that the upgrade cannot be performed on these maps, because the defect they
produce does not shrink in operator norm at all.  Nothing here assumes that
theorem or any part of it.

## Relation to the rest of the tree

`Sofic.NormTraceGap` proves the one-sided domination `‖·‖₂ ≤ ‖·‖` for the same
matrices, and observes that the reverse fails.  This file exhibits the failure
at the maps that matter, with both sides computed exactly rather than bounded.
`Analysis.AmenableQuasidiagonal` does the same for *permutation* models; the
present statement is about the compressions quasidiagonality actually asks
for.

`Algebra.Amenable.isAmenable_of_locallyFinite` places the class of
`Analysis.CompressionTraceLocallyFinite` --- where the operator-norm clause
*can* be achieved --- properly inside the amenable groups, which is why the
gap this file measures is a gap and not a vacuity.

## Manuscript status

Certifies no manuscript step.  It quantifies the distance between the elementary
construction and the cited theorem, unconditionally.
-/

namespace GroupApproximation
namespace Quasidiagonal

open Filter ReducedGroupCStarTrace
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

universe u

variable {G : Type u} [Group G]

local instance folnerDecidableEq : DecidableEq G := Classical.decEq G

/-! ## The escaping coordinates -/

/-- The window coordinates that `g` pushes out of the window.  Written with an
explicit `∃ p : Fin k` rather than with `Set.range`, so that the predicate is
decidable by instance search over the finite index type. -/
def escapeSet {k : ℕ} (e : Fin k → G) (g : G) : Finset (Fin k) :=
  Finset.univ.filter fun q ↦ ¬ ∃ p : Fin k, e p = g * e q

theorem mem_escapeSet {k : ℕ} {e : Fin k → G} {g : G} {q : Fin k} :
    q ∈ escapeSet e g ↔ g * e q ∉ Set.range e := by
  constructor
  · intro h hmem
    exact (Finset.mem_filter.mp h).2 (Set.mem_range.mp hmem)
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ q, ?_⟩
    intro hex
    exact h (Set.mem_range.mpr hex)

theorem mem_range_of_not_mem_escapeSet {k : ℕ} {e : Fin k → G} {g : G}
    {q : Fin k} (h : q ∉ escapeSet e g) : g * e q ∈ Set.range e :=
  not_not.mp fun hn ↦ h (mem_escapeSet.mpr hn)

/-! ## The defect in the Hilbert--Schmidt norm -/

/-- **The Hilbert--Schmidt size of the defect is exactly the proportion of
escaping coordinates.**

The defect is the diagonal projection onto the escaping coordinates
(`Analysis.CompressionTraceRigidity`), so its normalized squared
Hilbert--Schmidt norm counts them and divides by the dimension.  Compare
`one_le_norm_inverseDefect_of_not_mem_range`, which says the *operator* norm of
the same matrix is `1` as soon as the count is positive: a projection of rank
one in a space of dimension `k` has Hilbert--Schmidt size `1/k` and operator
norm `1`, and that discrepancy is the whole of the difficulty. -/
theorem hsNormSq_inverseDefect {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) (g : G) :
    hsNormSq (naturalFiniteModel k) (inverseDefect e g)
      = ((escapeSet e g).card : ℝ) / k := by
  classical
  have hinner : ∀ p : Fin k,
      (∑ q : Fin k, Complex.normSq (inverseDefect e g p q))
        = if p ∈ escapeSet e g then (1 : ℝ) else 0 := by
    intro p
    rw [Finset.sum_eq_single p]
    · by_cases hp : p ∈ escapeSet e g
      · rw [if_pos hp,
          inverseDefect_diag_of_not_mem_range he g (mem_escapeSet.mp hp)]
        simp
      · rw [if_neg hp, inverseDefect_apply_of_mem_range he g
          (mem_range_of_not_mem_escapeSet hp) p]
        simp
    · intro q _ hq
      by_cases hqe : q ∈ escapeSet e g
      · rw [inverseDefect_apply_of_not_mem_range_of_ne he g
          (mem_escapeSet.mp hqe) (Ne.symm hq)]
        simp
      · rw [inverseDefect_apply_of_mem_range he g
          (mem_range_of_not_mem_escapeSet hqe) p]
        simp
    · intro hcon
      exact absurd (Finset.mem_univ p) hcon
  have hsum : (∑ p : Fin k, ∑ q : Fin k,
      Complex.normSq (inverseDefect e g p q))
      = ((escapeSet e g).card : ℝ) := by
    rw [Finset.sum_congr rfl fun p _ ↦ hinner p, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  show (∑ p : Fin k, ∑ q : Fin k, Complex.normSq (inverseDefect e g p q))
      / (Fintype.card (naturalFiniteModel k) : ℝ) = _
  rw [hsum, card_naturalFiniteModel]

/-! ## Windows that are Følner sets -/

/-- The escaping coordinates of an enumerated window are the Følner boundary of
that window: `q` escapes exactly when `e q` lies in `A` and `g · e q` does
not. -/
theorem card_escapeSet_eq_card_boundary {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) (A : Finset G)
    (hA : ∀ x : G, x ∈ A ↔ x ∈ Set.range e) (g : G) :
    (escapeSet e g).card = (AmenableActionSofic.boundary A g).card := by
  classical
  have himg : (escapeSet e g).image e = AmenableActionSofic.boundary A g := by
    ext x
    rw [Finset.mem_image, AmenableActionSofic.mem_boundary]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(hA (e q)).mpr ⟨q, rfl⟩, fun hc ↦ mem_escapeSet.mp hq ((hA _).mp hc)⟩
    · rintro ⟨hx, hgx⟩
      obtain ⟨q, rfl⟩ := (hA x).mp hx
      exact ⟨q, mem_escapeSet.mpr fun hc ↦ hgx ((hA _).mpr hc), rfl⟩
  rw [← himg, Finset.card_image_of_injective _ he]

/-- **The Følner compressions are asymptotically multiplicative in the
`2`-norm.**

For a countable amenable group, a finite set of translations and any accuracy,
there is a compression whose Hilbert--Schmidt multiplicativity defect at every
prescribed pair `(λ_{g⁻¹}, λ_g)` is below that accuracy.  Its unitality,
complete positivity and trace clause are exact for every window
(`Analysis.CompressionTraceModel`), so this is a complete `2`-norm matrix model
of the canonical trace on any prescribed finite set. -/
theorem exists_folner_compression_of_isAmenable
    (hG : Amenability.IsAmenable G) (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (e : Fin k → G), 0 < k ∧ Function.Injective e ∧
      ∀ g ∈ S, hsNormSq (naturalFiniteModel k) (inverseDefect e g) < ε := by
  classical
  obtain ⟨A, hAne, hbd⟩ := AmenableActionSofic.exists_folner hG S hε
  obtain ⟨x₀, hx₀⟩ := hAne
  haveI : Nonempty A := ⟨⟨x₀, hx₀⟩⟩
  have heinj : Function.Injective
      (fun i : Fin (Fintype.card A) ↦ (((Fintype.equivFin A).symm i : A) : G)) := by
    intro i j hij
    exact (Fintype.equivFin A).symm.injective (Subtype.ext hij)
  have hA : ∀ x : G, x ∈ A ↔ x ∈ Set.range
      (fun i : Fin (Fintype.card A) ↦ (((Fintype.equivFin A).symm i : A) : G)) := by
    intro x
    constructor
    · intro hx
      exact ⟨Fintype.equivFin A ⟨x, hx⟩, by simp⟩
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin A).symm i).2
  have hApos : (0 : ℝ) < A.card := by
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨x₀, hx₀⟩
    exact_mod_cast hpos
  refine ⟨Fintype.card A,
    fun i ↦ (((Fintype.equivFin A).symm i : A) : G), Fintype.card_pos, heinj,
    fun g hg ↦ ?_⟩
  rw [hsNormSq_inverseDefect heinj g,
    card_escapeSet_eq_card_boundary heinj A hA g, Fintype.card_coe,
    div_lt_iff₀ hApos]
  exact hbd g hg

/-! ## The two norms at the same maps -/

/-- **An element of infinite order always has an escaping coordinate.**

If it had none, the window would be invariant under `g`, hence under every
power of `g`, and the stabilizer of a nonempty finite set is finite
(`finite_leftStabilizer`) --- so the powers of `g` could not be distinct. -/
theorem exists_not_mem_range_of_injective_pow {k : ℕ} (hk : 0 < k)
    {e : Fin k → G} (_he : Function.Injective e) {g : G}
    (hg : Function.Injective fun n : ℕ ↦ g ^ n) :
    ∃ q : Fin k, g * e q ∉ Set.range e := by
  classical
  by_contra hcon
  push Not at hcon
  have hmemW : ∀ x : G,
      x ∈ Finset.image e Finset.univ ↔ x ∈ Set.range e := by
    intro x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨q, -, rfl⟩
      exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, Finset.mem_univ q, rfl⟩
  have hWne : (Finset.image e Finset.univ).Nonempty := by
    obtain ⟨q⟩ := Fin.pos_iff_nonempty.mp hk
    exact ⟨e q, (hmemW _).mpr ⟨q, rfl⟩⟩
  have hgstab : g ∈ leftStabilizer (Finset.image e Finset.univ) := by
    rw [mem_leftStabilizer]
    intro x hx
    obtain ⟨q, rfl⟩ := (hmemW x).mp hx
    exact (hmemW _).mpr (hcon q)
  haveI : Finite (leftStabilizer (Finset.image e Finset.univ)) :=
    finite_leftStabilizer hWne
  have hinj : Function.Injective
      (fun n : ℕ ↦ (⟨g ^ n, pow_mem hgstab n⟩ :
        leftStabilizer (Finset.image e Finset.univ))) := by
    intro a b hab
    exact hg (congrArg Subtype.val hab)
  haveI : Finite ℕ := Finite.of_injective _ hinj
  exact not_finite ℕ

/-- **The gap, at one matrix.**

For a countable amenable group with an element `g` of infinite order --- `ℤ` is
the smallest example --- and any accuracy `ε`, there is a compression whose
multiplicativity defect at the pair `(λ_{g⁻¹}, λ_g)` has

* normalized Hilbert--Schmidt size below `ε`, and
* operator norm at least `1`.

Both clauses are about **the same matrix**, produced by the same map.  No
sharpening of the Følner set can help: the second clause holds at every window
whatever, by `exists_not_mem_range_of_injective_pow`.  This is the precise
sense in which the elementary route stops, and the precise size of what
Tikuisis--White--Winter supplies. -/
theorem exists_compression_hsNormSq_lt_and_one_le_norm
    (hG : Amenability.IsAmenable G) {g : G}
    (hg : Function.Injective fun n : ℕ ↦ g ^ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (e : Fin k → G), 0 < k ∧ Function.Injective e ∧
      hsNormSq (naturalFiniteModel k) (inverseDefect e g) < ε ∧
        1 ≤ ‖inverseDefect e g‖ := by
  classical
  obtain ⟨k, e, hkpos, heinj, hsmall⟩ :=
    exists_folner_compression_of_isAmenable hG {g} hε
  obtain ⟨q, hq⟩ := exists_not_mem_range_of_injective_pow hkpos heinj hg
  exact ⟨k, e, hkpos, heinj, hsmall g (Finset.mem_singleton_self g),
    one_le_norm_inverseDefect_of_not_mem_range heinj hq⟩

end

end Quasidiagonal
end GroupApproximation
