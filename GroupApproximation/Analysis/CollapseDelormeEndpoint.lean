import GroupApproximation.Analysis.RankNormalizedHilbertization

/-!
# The join, the nonvanishing of `β`, and the Delorme–Guichardet consumption

Proof-ledger rows `CO.21` (its nonvanishing clause) and `CO.21b`, the last two
paragraphs of the proof of `thm:projection-collapse` in
`non_mf_groups_exist.tex` (navigate by the label; the file is under concurrent
edit).

The printed text runs:

> Suppose `β(a) = 0` for every `a ∈ S`.  Put `r₁ = 1` and
> `r_i = ∏_{j<i}(1 - q_{a_j})` for `i ≥ 2`.  The products `e_i = r_i q_{a_i}`
> are projections with `e_i = r_i - r_{i+1}`, so they are pairwise orthogonal
> and `∑_i e_i = 1 - r_{m+1} = q`.  Each `d_{a_i}` commutes with `r_i`, so
> `e_i = (d_{a_i} r_i) d_{a_i}` and `Λ(e_i) = 0`, whence `Λ(q) = 0` against
> `‖Λ(q)‖ = 1`.  So `β` is not identically zero.
>
> By the Delorme–Guichardet theorem, `β` is a coboundary: there is `y ∈ K_q`
> with `β(g) = y - π(g) y`.  The hypothesis on `p` gives `d_{sas⁻¹} = 0`,
> hence `π(sas⁻¹) y = y`, for every `a ∈ L`.  The proof of
> `thm:kazhdan-transport` identifies `Fix π(sLs⁻¹)` with `Fix π(L)` … Hence
> `π(g) y = y` and `β(g) = 0` for every `g ∈ L`, contradicting the previous
> paragraph.

Everything in that text that is algebra is proved here; the two analytic
inputs are isolated as named hypotheses of the final theorem, and are named
again at the end of this docstring.

## The join

`partialComplement x i` is `r_i`, and `sum_partialComplement_mul` is the
printed telescoping `∑_{i<m} r_i x_i = 1 - r_m`, i.e. `∑_i e_i = q`.  It holds
in an arbitrary ring and needs no commutativity: `r_{i+1} = r_i - r_i x_i` is
`Finset.prod_range_succ` and `mul_sub`.

## Nonvanishing of `β`

`massNull_mul_left` is one-sided stability of `ker Λ`, the special case of
`RankNormalizedHilbertization.massNull_mul_mul` that the printed
`e_i = (d_{a_i} r_i) d_{a_i}` uses.  `massNull_join` combines it with the
telescoping: if every `Λ(d_{a_i})` vanishes then `Λ(q) = 0`.
`projection_not_massNull` is the contradiction with `‖Λ(q)‖ = 1`, so the
printed *"so `β` is not identically zero"* is closed as soon as `Λ` itself is
in hand.

## The Delorme–Guichardet consumption

`fixed_of_coboundary_eq_zero`, `eq_zero_of_fixed`,
`eq_zero_of_compressed_fixed` and `collapse_contradiction` are the last
paragraph, over an arbitrary complex module.  The compressed subgroup enters
as a monoid endomorphism `c : L →* L` — conjugation by `s`, which lands in
`L` because `s L s⁻¹ ⊆ L` is a printed hypothesis of the theorem.

None of these four uses multiplicativity of `π`, so `π` is carried as a plain
family of linear automorphisms; that keeps the statements independent of the
upgrade of `Analysis/CollapseCocycleAnalytic.conjQ` to a representation.

## What is still hypothesis, and why

`collapse_contradiction` takes two named hypotheses.

* `hdelorme`, that `β` is a coboundary.  Delorme–Guichardet is in the corpus,
  as `Kazhdan/DelormeFixedPoint.exists_fixed_point_of_hasKazhdanPropertyT`,
  but it is stated for a **complete real** Hilbert space, and `K_ω` is
  complex and is not proved complete: `Sofic/KOmegaHilbert` supplies
  `InnerProductSpace ℂ (KOmega …)` and claims no `CompleteSpace`.  Both gaps
  are real work — the ultraproduct-is-complete diagonal argument along `ω`,
  and a `ℂ`-to-`ℝ` transfer for which Mathlib at the pin offers neither an
  `InnerProductSpace ℝ` instance from an `InnerProductSpace ℂ` one nor a
  `LinearIsometryEquiv.restrictScalars`.
* `htransport`, the identification of `Fix π(sLs⁻¹)` with `Fix π(L)`.  The
  weighted transport theorem is invoked at `ν_n = k_n` in
  `Sofic/CollapseRankWeightTransport`; what is missing between that and
  `htransport` is the passage from the transported *commutant* statement to
  the equality of fixed subspaces inside `K_ω`.

Stating them as hypotheses rather than as axioms or placeholder binders is
deliberate: this file proves an implication, and the implication is exactly
the printed reasoning between those two inputs.
-/

namespace GroupApproximation
namespace CollapseDelormeEndpoint

open Filter Matrix Topology
open KazhdanCornerMatrices ScaledKazhdanTransport UltraproductModelConstruction
open RankNormalizedHilbertization KOmegaHilbert
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## The join of finitely many idempotents, and its telescoping -/

section RingTelescope

variable {A : Type*} [Ring A]

/-- The printed `r_i = ∏_{j < i} (1 - x_j)`. -/
def partialComplement (x : ℕ → A) (i : ℕ) : A :=
  ∏ j ∈ Finset.range i, (1 - x j)

@[simp] theorem partialComplement_zero (x : ℕ → A) :
    partialComplement x 0 = 1 := by
  unfold partialComplement
  exact Finset.prod_range_zero _

/-- The printed `e_i = r_i - r_{i+1}`, rearranged. -/
theorem partialComplement_succ (x : ℕ → A) (i : ℕ) :
    partialComplement x (i + 1)
      = partialComplement x i - partialComplement x i * x i := by
  unfold partialComplement
  rw [Finset.prod_range_succ, mul_sub, mul_one]

/-- **The printed telescoping.**  `∑_{i<m} e_i = 1 - r_m`, which is the join
`q` of the `x_i`.  No commutativity and no idempotence is used. -/
theorem sum_partialComplement_mul (x : ℕ → A) (m : ℕ) :
    ∑ i ∈ Finset.range m, partialComplement x i * x i
      = 1 - partialComplement x m := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, partialComplement_succ]
      abel

end RingTelescope

/-! ## One-sided stability of `ker Λ`, and the join -/

/-- Left multiplication by a uniformly bounded family preserves nullity: the
special case of `massNull_mul_mul` that the printed `e_i = (d_{a_i} r_i) d_{a_i}`
uses. -/
theorem massNull_mul_left (Y : ℕ → FiniteModel) (w : ℕ → ℝ)
    (ω : Ultrafilter ℕ) (A ξ : MatFam Y) (Ca : ℝ)
    (hA : ∀ n, ‖A n‖ ≤ Ca) (hξ : ξ ∈ massNull Y w ω) :
    (fun n ↦ A n * ξ n) ∈ massNull Y w ω := by
  intro ε hε
  have hCa : 0 ≤ Ca := (norm_nonneg (A 0)).trans (hA 0)
  obtain ⟨c, hcpos, hclt⟩ := exists_pos_mul_lt hε (Ca ^ 2)
  filter_upwards [hξ c hcpos] with n hn
  show matMass (A n * ξ n) ≤ ε * clipWeight w n
  have hclip : (0 : ℝ) ≤ clipWeight w n := clipWeight_nonneg w n
  have ha2 : ‖A n‖ ^ 2 ≤ Ca ^ 2 := by
    nlinarith [norm_nonneg (A n), hA n]
  calc matMass (A n * ξ n) ≤ ‖A n‖ ^ 2 * matMass (ξ n) :=
        matMass_mul_le_left (A n) (ξ n)
    _ ≤ Ca ^ 2 * matMass (ξ n) :=
        mul_le_mul_of_nonneg_right ha2 (matMass_nonneg _)
    _ ≤ Ca ^ 2 * (c * clipWeight w n) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (Ca ^ 2 * c) * clipWeight w n := by ring
    _ ≤ ε * clipWeight w n := mul_le_mul_of_nonneg_right hclt.le hclip

/-- **The printed nonvanishing step, null direction.**  If each `e_i = r_i x_i`
is a uniformly bounded left multiple of a null family `d_i` — which is the
printed `e_i = (d_{a_i} r_i) d_{a_i}` — then the join `q = 1 - r_m` is null. -/
theorem massNull_join (Y : ℕ → FiniteModel) (w : ℕ → ℝ) (ω : Ultrafilter ℕ)
    (m : ℕ) (x b d : ℕ → MatFam Y) (Cb : ℝ)
    (hb : ∀ i n, ‖b i n‖ ≤ Cb) (hd : ∀ i, d i ∈ massNull Y w ω)
    (he : ∀ i, partialComplement x i * x i = fun n ↦ b i n * d i n) :
    (1 : MatFam Y) - partialComplement x m ∈ massNull Y w ω := by
  rw [← sum_partialComplement_mul x m]
  apply Submodule.sum_mem
  intro i _
  rw [he i]
  exact massNull_mul_left Y w ω (b i) (d i) Cb (hb i) (hd i)

/-- The class of a null family is the zero vector of `K_ω`. -/
theorem mkK_eq_zero_of_massNull (Y : ℕ → FiniteModel) (w : ℕ → ℝ)
    (ω : Ultrafilter ℕ) (hw : ∀ n, 0 ≤ w n) (ξ : massBounded Y w)
    (hξ : (ξ : MatFam Y) ∈ massNull Y w ω) :
    mkK Y w ω hw ξ = 0 := by
  show (Submodule.Quotient.mk ξ : Vec Y w ω) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact hξ

/-- **The printed contradiction `Λ(q) = 0` against `‖Λ(q)‖ = 1`.**  A family of
orthogonal projections of positive rank is never null at its own rank weight.

Combined with `massNull_join`, this is the printed *"so `β` is not identically
zero"*: were every `Λ(d_a)` to vanish, `Λ(q)` would vanish, and it does
not. -/
theorem projection_not_massNull (Y : ℕ → FiniteModel) (ω : Ultrafilter ℕ)
    (P : MatFam Y) (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hrk : ∀ n, 0 < (P n).rank) :
    P ∉ massNull Y (rankWeight Y P) ω := by
  intro hnull
  have h0 : mkK Y (rankWeight Y P) ω (rankWeight_nonneg Y P)
      ⟨P, projection_mem_massBounded Y P hP⟩ = 0 :=
    mkK_eq_zero_of_massNull Y (rankWeight Y P) ω (rankWeight_nonneg Y P) _ hnull
  have h1 := norm_mkK_projection_mk Y ω P hP hrk
  rw [h0, norm_zero] at h1
  exact zero_ne_one h1

/-! ## The Delorme–Guichardet consumption -/

section Delorme

variable {L : Type*} [Group L] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- If `β` is the coboundary of `y` and `β a = 0`, then `y` is fixed by
`π a`.  This is the printed *"the hypothesis on `p` gives `d_{sas⁻¹} = 0`,
hence `π(sas⁻¹) y = y`"*. -/
theorem fixed_of_coboundary_eq_zero (π : L → (V ≃ₗ[ℂ] V)) (β : L → V) (y : V)
    (hy : ∀ g : L, β g = y - π g y) {a : L} (ha : β a = 0) : π a y = y := by
  have h := hy a
  rw [ha] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- Conversely, a fixed vector kills the coboundary: the printed *"hence
`π(g) y = y` and `β(g) = 0`"*. -/
theorem eq_zero_of_fixed (π : L → (V ≃ₗ[ℂ] V)) (β : L → V) (y : V)
    (hy : ∀ g : L, β g = y - π g y) {g : L} (hg : π g y = y) : β g = 0 := by
  rw [hy g, hg, sub_self]

/-- **The printed deduction, positive form.**  A primitive for `β` that is
fixed by the compressed subgroup is fixed by the whole of `L` once the
transport chain identifies the two fixed spaces, and then `β` vanishes
identically. -/
theorem eq_zero_of_compressed_fixed (π : L → (V ≃ₗ[ℂ] V)) (β : L → V) (y : V)
    (c : L →* L) (hy : ∀ g : L, β g = y - π g y)
    (hcompressed : ∀ a : L, β (c a) = 0)
    (htransport : (∀ a : L, π (c a) y = y) → ∀ g : L, π g y = y) :
    ∀ g : L, β g = 0 := fun g ↦
  eq_zero_of_fixed π β y hy
    (htransport
      (fun a ↦ fixed_of_coboundary_eq_zero π β y hy (hcompressed a)) g)

/-- **`CO.21b`: the printed contradiction.**

`hdelorme` is Delorme–Guichardet — `β` is a coboundary; `hcompressed` is the
printed `d_{sas⁻¹} = 0`; `htransport` is the identification of
`Fix π(sLs⁻¹)` with `Fix π(L)` that the weighted transport theorem supplies
at `ν_n = k_n`; `hne` is the nonvanishing of the previous paragraph.  The
conclusion is the printed contradiction, and everything between the
hypotheses is proved here.

The module docstring records precisely what each of the two analytic
hypotheses would take to discharge inside `K_ω`. -/
theorem collapse_contradiction (π : L → (V ≃ₗ[ℂ] V)) (β : L → V) (c : L →* L)
    (hdelorme : ∃ y : V, ∀ g : L, β g = y - π g y)
    (hcompressed : ∀ a : L, β (c a) = 0)
    (htransport : ∀ y : V, (∀ a : L, π (c a) y = y) → ∀ g : L, π g y = y)
    (hne : ∃ g : L, β g ≠ 0) : False := by
  obtain ⟨y, hy⟩ := hdelorme
  obtain ⟨g, hg⟩ := hne
  exact hg (eq_zero_of_compressed_fixed π β y c hy hcompressed (htransport y) g)

end Delorme

end

end CollapseDelormeEndpoint
end GroupApproximation
