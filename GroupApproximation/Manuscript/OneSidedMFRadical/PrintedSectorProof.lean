import GroupApproximation.Analysis.KazhdanProjectionOneSidedOrder
import GroupApproximation.Sofic.HyperlinearScalar
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# The printed proof of `thm:normal-kazhdan`, sentence by sentence

`non_mf_groups_exist.tex`, the proof of
`\begin{theorem}[normal Kazhdan radical theorem]\label{thm:normal-kazhdan}` in
`\section{Normal Kazhdan subgroups and the MF radical}`.  The manuscript is
under revision, so this module is anchored on labels, not line numbers.

`Sofic/CoronaImageNormalKazhdan.lean` already certifies `thm:normal-kazhdan`
unconditionally, but along the *moving-corner* route (`nk_01`…`nk_05`).  The
printed proof of Section 4 runs differently: after the corner
`q 𝒬_d q` is produced it argues with a **corner Kazhdan inequality** and a
**normalized trace**, and five of its sentences had no Lean declaration
attached.  A referee reading Section 4 line by line therefore had nothing to
check against for

1. "In the corner `q 𝒬_d q`, the Kazhdan projection is zero."
2. "Hence the positive element `b = |S|⁻¹ ∑_{s∈S} (qΘ(s)q - q)^*(qΘ(s)q - q)`
   satisfies `b ≥ (κ²/|S|) q`."
3. "Indeed, in every representation of the corner there are no `K`-fixed
   vectors, so the defining Kazhdan inequality gives this operator
   inequality."
4. "Taking the normalized trace on `q_n M_{d_n}(ℂ) q_n` yields
   `|S|⁻¹ ∑_{s∈S} ‖W_n(s) - q_n‖₂² ≥ κ²/|S| - o(1)`. … The order inequality
   for `b` says that the negative part of `b_n - (κ²/|S|) q_n` converges to
   zero in operator norm, which gives the displayed trace inequality."
5. "After passing to a subsequence, one fixed `s₀ ∈ S` therefore stays a
   positive Hilbert–Schmidt distance from the corner identity."

This module supplies one named declaration per sentence and one closed
proposition bundling them.

## How the order `b ≥ (κ²/|S|) q` is spelled, and why

The repository's usual device for an order relation without a global order
instance is the absorption identity: `Manuscript/OneSidedMFRadical/
StableFiniteness.lean` writes `p ≤ q` as `q * p = p`, and
`Analysis/CoronaProjectionOrder.lean` explains at length that this keeps the
corona statements free of the `[PartialOrder]` `[StarOrderedRing]` side
instances, which for a C-star algebra come from `CStarAlgebra.spectralOrder`
rather than from instance search.

That device is unavailable here, for a mathematical reason rather than a
technical one: `b` is a **positive element** of the corner, not a projection,
so `b ≥ c·q` is not a comparison of projections and no absorption identity
expresses it.  The instance-free reading of `≥` for a self-adjoint element is
its **quadratic form**, and that is the spelling used below:

    `κ²/|S| · ‖x‖² ≤ |S|⁻¹ ∑_{s∈S} ‖ρ(s)x - x‖²`   for every corner vector `x`.

Two further reasons make this the right choice rather than a fallback.  It is
literally what the printed *proof* of the inequality produces — the defining
Kazhdan inequality is a statement about vectors — and it is literally what the
printed *use* of the inequality consumes, since `‖ρ(s)x - x‖² =
⟪(ρ(s)-1)^*(ρ(s)-1)x, x⟫` and the trace step below averages that quadratic
form over an orthonormal basis.  So no information is lost in either
direction, and no order instance is installed anywhere in this file.

`le_of_le_in_faithful_rep`, by contrast, *does* use a genuine order: the
Loewner order on `B(H)`, which Mathlib installs, on the hypothesis side, and
delivers the absorption identity `q * p = q` on the conclusion side, in an
abstract `C*`-algebra that carries no order.  That is exactly the printed
passage of `lem:kazhdan-projection-order` — "faithfulness of the
representation gives the same projection inequality in `B`".

## What is proved

* `complement_mul_kazhdanProjection`, `kazhdanProjection_mul_complement`,
  `corner_compression_kazhdanProjection` — sentence 1, in the algebra: with
  `q = 1 - p` the compression `q p q` of the Kazhdan projection to the corner
  is zero.
* `eq_zero_of_mem_corner_of_fixed` — sentence 1, on vectors: a vector of the
  corner cut by `q = 1 - p`, with `p` the projection onto the fixed vectors,
  that is fixed by the whole group is zero.  This is what "the corner has no
  nonzero `K`-fixed vectors" says.
* `kazhdan_sum_sq_ge_of_noInvariant`, `kazhdan_average_sq_ge_of_noInvariant`,
  `corner_kazhdan_average_sq_ge` — sentences 2 and 3: the corner Kazhdan
  inequality, first from a bare no-invariant-vectors hypothesis and then on
  the corner itself, `(Fix ρ)ᗮ`, where the hypothesis is discharged by
  `KazhdanOrthogonal.orthogonalRepresentation_hasNoInvariantVectors`.
* `hsNormSq_sum_ge_of_corner_quadratic_form`,
  `printed_corner_trace_inequality` — sentence 4: the passage from the corner
  order inequality to the normalized trace.  The normalized trace of
  `(W - 1)^*(W - 1)` is `hsNormSq`, so the printed displayed inequality is the
  conclusion verbatim, with the printed `o(1)` carried by the constant: taking
  `c = κ² - ε` gives `κ²/|S| - ε/|S|` on the left.
* `exists_persistent_index`, `exists_persistent_index_atTop` — sentence 5:
  from a lower bound on the `S`-average at every coordinate, one fixed
  `s₀ ∈ S` realizes the bound along an infinite set of coordinates.  "After
  passing to a subsequence" is read as "along infinitely many coordinates",
  which is what `exists_persistent_index` states; `exists_persistent_index_atTop`
  is the same fact in tail form.
* `mul_eq_of_isStarProjection_le`, `le_of_le_in_faithful_rep` — the sixth,
  separate row: the faithful-representation bridge of
  `lem:kazhdan-projection-order`, which the docstring of
  `Analysis/KazhdanProjectionOneSidedOrder.lean` deliberately leaves open under
  *Not claimed*.  `mul_eq_of_isStarProjection_le` is the converse of that
  file's `le_of_isStarProjection_mul_eq`.
* `PrintedNormalKazhdanCornerSteps` / `manuscriptPrintedNormalKazhdanCornerSteps`
  — the five sentences as one closed proposition.

## What is not claimed

The bridge between the abstract-Hilbert-space form of the corner Kazhdan
inequality (`corner_kazhdan_average_sq_ge`, over `ℝ`, as the repository's
`IsKazhdanPair` API demands) and the coordinate quadratic form over `ℂ^{q_n}`
that `hsNormSq_sum_ge_of_corner_quadratic_form` consumes.  That bridge is not
a scalar-restriction triviality: at the coordinate level `W_n` is only an
*asymptotic* representation, so no Kazhdan pair applies to it directly, and the
passage is exactly the printed sentence "the coordinate elements `b_n` …
represent `b`", i.e. the corona quotient.  Nothing below asserts it; the trace
step therefore takes the coordinate inequality as its hypothesis, which is the
printed implication at the coordinate level and nothing more.

## Manuscript status

Supplies the five previously unattached sentences of the printed proof of
`thm:normal-kazhdan`, plus the faithful-representation clause of
`lem:kazhdan-projection-order`.  The endpoint of `thm:normal-kazhdan` itself is
unchanged and remains `CoronaImageNormalKazhdan`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Matrix

universe u v

/-! ## Sentence 1 — in the corner, the Kazhdan projection is zero

`p` is the image of the Kazhdan projection of `K` in the corona and
`q = 1 - p`.  The compression of `p` to `q 𝒬_d q` is `q p q`, and it vanishes
for the same reason in every unital ring: `q` and `p` annihilate each other. -/

/-- `q p = 0` for `q = 1 - p`. -/
theorem complement_mul_kazhdanProjection {A : Type*} [Ring A] {p : A}
    (hp : IsIdempotentElem p) : (1 - p) * p = 0 := by
  rw [sub_mul, one_mul, hp.eq, sub_self]

/-- `p q = 0` for `q = 1 - p`. -/
theorem kazhdanProjection_mul_complement {A : Type*} [Ring A] {p : A}
    (hp : IsIdempotentElem p) : p * (1 - p) = 0 := by
  rw [mul_sub, mul_one, hp.eq, sub_self]

/-- **"In the corner `q 𝒬_d q`, the Kazhdan projection is zero."**  The
compression of `p` to the corner cut by `q = 1 - p` vanishes. -/
theorem corner_compression_kazhdanProjection {A : Type*} [Ring A] {p : A}
    (hp : IsIdempotentElem p) : (1 - p) * p * (1 - p) = 0 := by
  rw [complement_mul_kazhdanProjection hp, zero_mul]

/-- **The same sentence on vectors: the corner has no nonzero `K`-fixed
vector.**  `p` is the orthogonal projection onto the fixed vectors of `ρ`, the
hypothesis `hq` says that `x` lies in the corner cut by `q = 1 - p`, and `hfix`
says that `x` is fixed.  Then `x = 0`.

This is the sentence the corner Kazhdan inequality is deduced from: "in every
representation of the corner there are no `K`-fixed vectors". -/
theorem eq_zero_of_mem_corner_of_fixed {K : Type u} [Group K] {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (rho : K →* (E ≃ₗᵢ[ℝ] E)) {x : E}
    (hq : x - (KazhdanOrthogonal.invariantSubmodule rho).starProjection x = x)
    (hfix : ∀ g : K, rho g x = x) : x = 0 := by
  have hzero : (KazhdanOrthogonal.invariantSubmodule rho).starProjection x = 0 :=
    sub_eq_self.mp hq
  have hmem : x ∈ KazhdanOrthogonal.invariantSubmodule rho :=
    (KazhdanOrthogonal.mem_invariantSubmodule rho x).mpr hfix
  have hself : (KazhdanOrthogonal.invariantSubmodule rho).starProjection x = x :=
    Submodule.starProjection_eq_self_iff.mpr hmem
  rw [hzero] at hself
  exact hself.symm

/-! ## Sentences 2 and 3 — the corner Kazhdan inequality

`b = |S|⁻¹ ∑_{s∈S} (qΘ(s)q - q)^*(qΘ(s)q - q)` satisfies `b ≥ (κ²/|S|) q`.
In quadratic form — see the module docstring for why that spelling — this
says that for every corner vector `x`,

    `κ²/|S| · ‖x‖² ≤ |S|⁻¹ ∑_{s∈S} ‖ρ(s)x - x‖²`,

and the printed justification is the defining Kazhdan inequality applied in a
representation with no invariant vectors. -/

/-- **The corner Kazhdan inequality, unnormalized.**  In a representation with
no nonzero invariant vector, the Kazhdan pair `(S, κ)` forces the total squared
displacement over `S` to dominate `κ²‖x‖²`.

The single input is `IsKazhdanPair.exists_moved_mul_norm_of_noInvariant`: one
element of `S` moves `x` by at least `κ‖x‖`, and the remaining summands are
nonnegative. -/
theorem kazhdan_sum_sq_ge_of_noInvariant {K : Type u} [Group K] {S : Finset K}
    {kappa : ℝ} (hS : IsKazhdanPair.{u, v} K S kappa) {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (rho : K →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors K rho) (x : E) :
    kappa ^ 2 * ‖x‖ ^ 2 ≤ ∑ s ∈ S, ‖rho s x - x‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hz : kappa ^ 2 * ‖(0 : E)‖ ^ 2 = 0 := by simp
    rw [hz]
    exact Finset.sum_nonneg fun s _ ↦ sq_nonneg _
  obtain ⟨s₀, hs₀, hmove⟩ :=
    hS.exists_moved_mul_norm_of_noInvariant rho hno x hx
  have hnn : 0 ≤ kappa * ‖x‖ := mul_nonneg hS.1.le (norm_nonneg x)
  have hsq : (kappa * ‖x‖) ^ 2 ≤ ‖rho s₀ x - x‖ ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hnn hmove
  have hterm : ‖rho s₀ x - x‖ ^ 2 ≤ ∑ s ∈ S, ‖rho s x - x‖ ^ 2 :=
    Finset.single_le_sum (f := fun s : K ↦ ‖rho s x - x‖ ^ 2)
      (fun s _ ↦ sq_nonneg _) hs₀
  calc kappa ^ 2 * ‖x‖ ^ 2 = (kappa * ‖x‖) ^ 2 := by ring
    _ ≤ ‖rho s₀ x - x‖ ^ 2 := hsq
    _ ≤ ∑ s ∈ S, ‖rho s x - x‖ ^ 2 := hterm

/-- **The corner Kazhdan inequality, in the printed normalization.**  Dividing
by `|S|` puts the constant where the manuscript prints it: `κ²/|S|`. -/
theorem kazhdan_average_sq_ge_of_noInvariant {K : Type u} [Group K]
    {S : Finset K} {kappa : ℝ} (hS : IsKazhdanPair.{u, v} K S kappa)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (rho : K →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors K rho) (x : E) :
    kappa ^ 2 / S.card * ‖x‖ ^ 2
      ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, ‖rho s x - x‖ ^ 2 := by
  have hnn : (0 : ℝ) ≤ ((S.card : ℝ))⁻¹ := by positivity
  calc kappa ^ 2 / S.card * ‖x‖ ^ 2
      = (S.card : ℝ)⁻¹ * (kappa ^ 2 * ‖x‖ ^ 2) := by ring
    _ ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, ‖rho s x - x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (kazhdan_sum_sq_ge_of_noInvariant hS rho hno x) hnn

/-- **The corner Kazhdan inequality, on the corner.**  The corner is
`(Fix ρ)ᗮ`, the range of `q = 1 - p`, and the no-invariant-vectors hypothesis
is discharged there by
`KazhdanOrthogonal.orthogonalRepresentation_hasNoInvariantVectors` — the
formal content of sentence 1 read as the input to sentence 3. -/
theorem corner_kazhdan_average_sq_ge {K : Type u} [Group K] {S : Finset K}
    {kappa : ℝ} (hS : IsKazhdanPair.{u, v} K S kappa) {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (rho : K →* (E ≃ₗᵢ[ℝ] E))
    (x : (KazhdanOrthogonal.invariantSubmodule rho)ᗮ) :
    kappa ^ 2 / S.card * ‖x‖ ^ 2
      ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S,
          ‖KazhdanOrthogonal.orthogonalRepresentation rho s x - x‖ ^ 2 :=
  kazhdan_average_sq_ge_of_noInvariant hS
    (KazhdanOrthogonal.orthogonalRepresentation rho)
    (KazhdanOrthogonal.orthogonalRepresentation_hasNoInvariantVectors rho) x

/-! ## Sentence 4 — the normalized trace of the corner

The coordinate elements are `b_n = |S|⁻¹ ∑_{s∈S} (W_n(s) - q_n)^*(W_n(s) - q_n)`
on `q_n M_{d_n}(ℂ) q_n`, where `q_n` is the identity of the corner.  Taking the
normalized trace of the corner turns `τ((W - 1)^*(W - 1))` into
`hsNormSq Y (W - 1)`, so the printed displayed inequality

    `|S|⁻¹ ∑_{s∈S} ‖W_n(s) - q_n‖₂² ≥ κ²/|S| - o(1)`

is the conclusion of `printed_corner_trace_inequality` verbatim, with the
printed `o(1)` carried by the constant.

The printed justification — "the negative part of `b_n - (κ²/|S|) q_n`
converges to zero in operator norm, which gives the displayed trace
inequality" — is exactly the implication proved here, at the coordinate level:
a lower bound on the quadratic form of `b_n` gives a lower bound on its
normalized trace.  The proof is the only one available without an order
instance, and is the standard one: evaluate the quadratic form on each
standard basis vector and average.  Column `j` of `W - 1` is
`(W - 1) *ᵥ e_j`, so the average of the quadratic form over the basis is
precisely the normalized Hilbert–Schmidt mass. -/

/-- **From the corner order inequality to the normalized trace.**  If the
quadratic form of `b = ∑_{s∈S} (W s - 1)^*(W s - 1)` dominates `c` on every
vector, then the normalized trace of `b` — that is, `∑_{s∈S} ‖W s - 1‖₂²` —
is at least `c`.

`hsNormSq Y A` is the normalized squared Hilbert–Schmidt norm
`(∑_{i,j} |A_{ij}|²)/|Y|`, so with `Y` the corner model and `1 = q_n` the
statement is the printed one with `|S|` still on the right; the printed
normalization is `printed_corner_trace_inequality`. -/
theorem hsNormSq_sum_ge_of_corner_quadratic_form (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) {ι : Type*} (S : Finset ι)
    (W : ι → Matrix Y Y ℂ) (c : ℝ)
    (h : ∀ x : Y → ℂ, c * ∑ i : Y, Complex.normSq (x i)
      ≤ ∑ s ∈ S, ∑ i : Y, Complex.normSq ((W s *ᵥ x - x) i)) :
    c ≤ ∑ s ∈ S, hsNormSq Y (W s - 1) := by
  have hcard : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hentry : ∀ (C : Matrix Y Y ℂ) (j k : Y),
      (C *ᵥ Pi.single j (1 : ℂ)) k = C k j := by
    intro C j k
    rw [Matrix.mulVec_single_one]
    rfl
  have hdiff : ∀ (s : ι) (j i : Y),
      (((W s *ᵥ (Pi.single j (1 : ℂ) : Y → ℂ)) -
          (Pi.single j (1 : ℂ) : Y → ℂ)) i) = (W s - 1) i j := by
    intro s j i
    have h1 : (W s *ᵥ (Pi.single j (1 : ℂ) : Y → ℂ)) -
          (Pi.single j (1 : ℂ) : Y → ℂ)
        = (W s - 1) *ᵥ (Pi.single j (1 : ℂ) : Y → ℂ) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [congrFun h1 i, hentry (W s - 1) j i]
  have hunit : ∀ j : Y,
      (∑ i : Y, Complex.normSq ((Pi.single j (1 : ℂ) : Y → ℂ) i)) = 1 := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hcol : ∀ j : Y,
      c ≤ ∑ s ∈ S, ∑ i : Y, Complex.normSq ((W s - 1) i j) := by
    intro j
    have hx := h (Pi.single j (1 : ℂ))
    rw [hunit j, mul_one] at hx
    have heq : ∑ s ∈ S, ∑ i : Y,
          Complex.normSq
            (((W s *ᵥ (Pi.single j (1 : ℂ) : Y → ℂ)) -
              (Pi.single j (1 : ℂ) : Y → ℂ)) i)
        = ∑ s ∈ S, ∑ i : Y, Complex.normSq ((W s - 1) i j) := by
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hdiff s j i]
    exact hx.trans_eq heq
  have hsum : (Fintype.card Y : ℝ) * c
      ≤ ∑ j : Y, ∑ s ∈ S, ∑ i : Y, Complex.normSq ((W s - 1) i j) := by
    calc (Fintype.card Y : ℝ) * c = ∑ _j : Y, c := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun j _ ↦ hcol j
  have hswap : ∑ j : Y, ∑ s ∈ S, ∑ i : Y, Complex.normSq ((W s - 1) i j)
      = ∑ s ∈ S, ∑ i : Y, ∑ j : Y, Complex.normSq ((W s - 1) i j) := by
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun s _ ↦ ?_)
    exact Finset.sum_comm
  have hRHS : ∑ s ∈ S, hsNormSq Y (W s - 1)
      = (∑ s ∈ S, ∑ i : Y, ∑ j : Y, Complex.normSq ((W s - 1) i j))
          / (Fintype.card Y : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ ↦ rfl
  rw [hRHS, le_div_iff₀ hcard]
  calc c * (Fintype.card Y : ℝ) = (Fintype.card Y : ℝ) * c := mul_comm _ _
    _ ≤ ∑ j : Y, ∑ s ∈ S, ∑ i : Y, Complex.normSq ((W s - 1) i j) := hsum
    _ = _ := hswap

/-- **The printed trace inequality.**  With `Y` the corner `q_n M_{d_n}(ℂ) q_n`,
`1 = q_n` its identity, `W s = W_n(s)` and `c = κ² - o(1)`, this is

    `|S|⁻¹ ∑_{s∈S} ‖W_n(s) - q_n‖₂² ≥ κ²/|S| - o(1)`,

the manuscript's displayed inequality, with `‖·‖₂` the normalized
Hilbert–Schmidt norm of the corner (`hsNormSq`). -/
theorem printed_corner_trace_inequality (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) {ι : Type*} (S : Finset ι)
    (W : ι → Matrix Y Y ℂ) (c : ℝ)
    (h : ∀ x : Y → ℂ, c * ∑ i : Y, Complex.normSq (x i)
      ≤ ∑ s ∈ S, ∑ i : Y, Complex.normSq ((W s *ᵥ x - x) i)) :
    c / S.card ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, hsNormSq Y (W s - 1) := by
  have hnn : (0 : ℝ) ≤ ((S.card : ℝ))⁻¹ := by positivity
  calc c / S.card = (S.card : ℝ)⁻¹ * c := by ring
    _ ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, hsNormSq Y (W s - 1) :=
        mul_le_mul_of_nonneg_left
          (hsNormSq_sum_ge_of_corner_quadratic_form Y hY S W c h) hnn

/-! ## Sentence 5 — one fixed generator survives

"After passing to a subsequence, one fixed `s₀ ∈ S` therefore stays a positive
Hilbert–Schmidt distance from the corner identity."

The average over the finite set `S` is bounded below at every coordinate, so at
every coordinate *some* element of `S` realizes the bound; `S` is finite and
the coordinates are infinite, so one element realizes it infinitely often.
"Passing to a subsequence" is read as "along an infinite set of coordinates",
which is `exists_persistent_index`; `exists_persistent_index_atTop` restates
that in tail form. -/

/-- **One element of `S` realizes the bound along infinitely many
coordinates.** -/
theorem exists_persistent_index {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ℕ → ι → ℝ) (c : ℝ)
    (h : ∀ n : ℕ, c ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, f n s) :
    ∃ s₀ ∈ S, {n : ℕ | c ≤ f n s₀}.Infinite := by
  have hcard : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hne : ((S.card : ℝ)) ≠ 0 := ne_of_gt hcard
  have hstep : ∀ n : ℕ, ∃ s ∈ S, c ≤ f n s := by
    intro n
    by_contra hcon
    have hlt : ∀ s ∈ S, f n s < c := by
      intro s hs
      by_contra hge
      exact hcon ⟨s, hs, not_lt.mp hge⟩
    have hsum : ∑ s ∈ S, f n s < ∑ _s ∈ S, c :=
      Finset.sum_lt_sum_of_nonempty hS hlt
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hmul : (S.card : ℝ)⁻¹ * ∑ s ∈ S, f n s
        < (S.card : ℝ)⁻¹ * ((S.card : ℝ) * c) :=
      mul_lt_mul_of_pos_left hsum (inv_pos.mpr hcard)
    have heq : (S.card : ℝ)⁻¹ * ((S.card : ℝ) * c) = c := by
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [heq] at hmul
    exact absurd (h n) (not_le.mpr hmul)
  by_contra hcon
  have hfin : ∀ s ∈ (S : Set ι), {n : ℕ | c ≤ f n s}.Finite := by
    intro s hs
    by_contra hinf
    exact hcon ⟨s, Finset.mem_coe.mp hs, hinf⟩
  have hsub : (Set.univ : Set ℕ) ⊆ ⋃ s ∈ (S : Set ι), {n : ℕ | c ≤ f n s} := by
    intro n _
    obtain ⟨s, hs, hns⟩ := hstep n
    exact Set.mem_biUnion (Finset.mem_coe.mpr hs) hns
  have hbig : (⋃ s ∈ (S : Set ι), {n : ℕ | c ≤ f n s}).Finite :=
    Set.Finite.biUnion S.finite_toSet hfin
  exact Set.infinite_univ (α := ℕ) (Set.Finite.subset hbig hsub)

/-- **The same, in tail form.**  Beyond every coordinate there is a later one at
which the fixed `s₀` still realizes the bound; this is what "stays a positive
Hilbert–Schmidt distance from the corner identity" asserts once the subsequence
has been taken. -/
theorem exists_persistent_index_atTop {ι : Type*} (S : Finset ι)
    (hS : S.Nonempty) (f : ℕ → ι → ℝ) (c : ℝ)
    (h : ∀ n : ℕ, c ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, f n s) :
    ∃ s₀ ∈ S, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c ≤ f n s₀ := by
  obtain ⟨s₀, hs₀, hinf⟩ := exists_persistent_index S hS f c h
  refine ⟨s₀, hs₀, fun N ↦ ?_⟩
  by_contra hno
  have hsubset : {n : ℕ | c ≤ f n s₀} ⊆ {i : ℕ | i < N} := by
    intro n hn
    by_contra hlt
    exact hno ⟨n, not_lt.mp hlt, hn⟩
  exact hinf (Set.Finite.subset (Set.finite_lt_nat N) hsubset)

/-! ## The faithful-representation bridge of `lem:kazhdan-projection-order`

> Faithfulness of the representation gives the same projection inequality in
> `B`.

`Analysis/KazhdanProjectionOneSidedOrder.lean` proves `U^* P U ≤ P` on a
Hilbert space and records under *Not claimed* that the passage from `B(H)` back
to an abstract unital `C*`-algebra `B` is left open.  This is that passage: the
Loewner inequality between the images of two projections under an injective
`*`-homomorphism gives the absorption identity `q p = q` in `B` itself, which
is how `Manuscript/OneSidedMFRadical/KazhdanProjectionOrder.lean` writes
projection order in an algebra carrying no order instance. -/

/-- **Loewner order between star projections is absorption.**  This is the
converse of `KazhdanProjectionOneSidedOrder.le_of_isStarProjection_mul_eq`,
proved by the same engine: for symmetric projections the Loewner order is
inclusion of ranges, and a projection fixes its own range. -/
theorem mul_eq_of_isStarProjection_le {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {P Q : E →L[𝕜] E} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (h : Q ≤ P) : P * Q = Q := by
  rw [← ContinuousLinearMap.coe_le_coe_iff] at h
  have hrange := ((ContinuousLinearMap.IsStarProjection.isSymmetricProjection
    hQ).le_iff_range_le_range
      (ContinuousLinearMap.IsStarProjection.isSymmetricProjection hP)).mp h
  refine ContinuousLinearMap.ext fun x ↦ ?_
  obtain ⟨z, hz⟩ := hrange (LinearMap.mem_range_self _ x)
  have hz' : P z = Q x := hz
  have hidem : P (P z) = P z :=
    congrArg (fun T : E →L[𝕜] E ↦ T z) hP.isIdempotentElem.eq
  show P (Q x) = Q x
  rw [← hz', hidem]

/-- **"Faithfulness of the representation gives the same projection inequality
in `B`."**  If a faithful `*`-representation of a unital `C*`-algebra sends the
projection `q` below the projection `p` in the Loewner order of `B(H)`, then
`q p = q` in `B`.

The hypothesis uses the genuine order that Mathlib installs on `B(H)`; the
conclusion is the absorption identity, which is how projection order is written
in `B`, where no order instance is available.  Both `p q = q` and `q p = q` are
available: they are stars of one another, since `p` and `q` are self-adjoint. -/
theorem le_of_le_in_faithful_rep {B : Type*} [CStarAlgebra B] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : Function.Injective pi) {p q : B}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hle : pi q ≤ pi p) :
    q * p = q := by
  have hPidem : IsIdempotentElem (pi p) := by
    show pi p * pi p = pi p
    rw [← map_mul, hp.isIdempotentElem.eq]
  have hPsa : IsSelfAdjoint (pi p) := by
    show star (pi p) = pi p
    rw [← map_star pi p, hp.isSelfAdjoint.star_eq]
  have hQidem : IsIdempotentElem (pi q) := by
    show pi q * pi q = pi q
    rw [← map_mul, hq.isIdempotentElem.eq]
  have hQsa : IsSelfAdjoint (pi q) := by
    show star (pi q) = pi q
    rw [← map_star pi q, hq.isSelfAdjoint.star_eq]
  have hmul : pi p * pi q = pi q :=
    mul_eq_of_isStarProjection_le ⟨hPidem, hPsa⟩ ⟨hQidem, hQsa⟩ hle
  have hpq : p * q = q := by
    apply hpi
    rw [map_mul]
    exact hmul
  have hstar := congrArg star hpq
  rwa [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] at hstar

/-! ## The five sentences as one closed proposition -/

/-- **The five previously unattached sentences of the printed proof of
`thm:normal-kazhdan`, as one proposition.**  In the printed order:

1. the compression of the Kazhdan projection `p` to the corner cut by
   `q = 1 - p` is zero;
2. that corner carries no nonzero fixed vector;
3. the corner Kazhdan inequality `b ≥ (κ²/|S|) q`, in its quadratic-form
   spelling — see the module docstring;
4. the normalized trace of the corner, `|S|⁻¹ ∑_{s∈S} ‖W(s) - q‖₂² ≥ c/|S|`,
   from the coordinate form of the order inequality, with the printed `o(1)`
   carried by `c`;
5. one fixed `s₀ ∈ S` realizes the bound at arbitrarily late coordinates.

Clause 4 takes the coordinate quadratic-form inequality as a hypothesis rather
than deriving it from clause 3: the corona passage that carries the corner
order inequality down to the coordinates is not claimed anywhere in this file,
for the reason recorded in the module docstring. -/
def PrintedNormalKazhdanCornerSteps : Prop :=
  (∀ (A : Type) [Ring A] (p : A), IsIdempotentElem p →
      (1 - p) * p = 0 ∧ (1 - p) * p * (1 - p) = 0) ∧
    (∀ (K : Type) [Group K] (E : Type) [NormedAddCommGroup E]
        [InnerProductSpace ℝ E] [CompleteSpace E]
        (rho : K →* (E ≃ₗᵢ[ℝ] E)) (x : E),
        x - (KazhdanOrthogonal.invariantSubmodule rho).starProjection x = x →
        (∀ g : K, rho g x = x) → x = 0) ∧
    (∀ (K : Type) [Group K] (S : Finset K) (kappa : ℝ),
        IsKazhdanPair.{0, 0} K S kappa →
        ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [CompleteSpace E] (rho : K →* (E ≃ₗᵢ[ℝ] E))
          (x : (KazhdanOrthogonal.invariantSubmodule rho)ᗮ),
          kappa ^ 2 / S.card * ‖x‖ ^ 2
            ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S,
                ‖KazhdanOrthogonal.orthogonalRepresentation rho s x - x‖ ^ 2) ∧
    (∀ (Y : FiniteModel), 0 < Fintype.card Y →
        ∀ (ι : Type) (S : Finset ι) (W : ι → Matrix Y Y ℂ) (c : ℝ),
          (∀ x : Y → ℂ, c * ∑ i : Y, Complex.normSq (x i)
            ≤ ∑ s ∈ S, ∑ i : Y, Complex.normSq ((W s *ᵥ x - x) i)) →
          c / S.card ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, hsNormSq Y (W s - 1)) ∧
    (∀ (ι : Type) (S : Finset ι), S.Nonempty →
        ∀ (f : ℕ → ι → ℝ) (c : ℝ),
          (∀ n : ℕ, c ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, f n s) →
          ∃ s₀ ∈ S, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c ≤ f n s₀)

/-- Closed proof of the five printed sentences. -/
theorem manuscriptPrintedNormalKazhdanCornerSteps :
    PrintedNormalKazhdanCornerSteps := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A _ p hp
    exact ⟨complement_mul_kazhdanProjection hp,
      corner_compression_kazhdanProjection hp⟩
  · intro K _ E _ _ _ rho x hq hfix
    exact eq_zero_of_mem_corner_of_fixed rho hq hfix
  · intro K _ S kappa hS E _ _ _ rho x
    exact corner_kazhdan_average_sq_ge hS rho x
  · intro Y hY ι S W c h
    exact printed_corner_trace_inequality Y hY S W c h
  · intro ι S hS f c h
    exact exists_persistent_index_atTop S hS f c h

end OneSidedMFRadical
end Manuscript
end GroupApproximation
