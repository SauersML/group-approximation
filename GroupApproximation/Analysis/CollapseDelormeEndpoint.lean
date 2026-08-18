import GroupApproximation.Analysis.RankNormalizedHilbertization
import GroupApproximation.Kazhdan.DelormeFixedPoint
import GroupApproximation.Kazhdan.KazhdanComplex

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
in an arbitrary ring and needs no commutativity, which is why `r_i` is a
recursion and not a `Finset.prod`: `Finset.prod` would demand a `CommMonoid`,
and the printed product `∏_{j<i}(1 - q_{a_j})` is an *ordered* one.  With the
recursion, `r_{i+1} = r_i - r_i x_i` is `mul_sub` and `mul_one`.

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
as a plain map `c : L → L` — conjugation by `s`, which lands in
`L` because `s L s⁻¹ ⊆ L` is a printed hypothesis of the theorem.

None of these four uses multiplicativity of `π`, so `π` is carried as a plain
family of linear automorphisms; that keeps the statements independent of the
upgrade of `Analysis/CollapseCocycleAnalytic.conjQ` to a representation.

## Delorme–Guichardet is not a literature input here

The printed step cites `\cite[Theorem 2.12.4]{BHV}`.  It does not have to be
cited: `Kazhdan/DelormeFixedPoint.exists_fixed_point_of_hasKazhdanPropertyT`
proves it in the corpus, for a **complete real** Hilbert space, and
`exists_primitive_of_hasKazhdanPropertyT` below carries it to the complex
case, which is the case the collapse needs.  The complex-to-real passage is
not hand-built: `Kazhdan/KazhdanComplex.realifyHom` already reads a unitary
representation as an orthogonal representation of the underlying real
Hilbert space, with the same norm, and `IsKazhdanPair.toComplex` already uses
exactly this idiom.  So `collapse_contradiction_of_hasKazhdanPropertyT` needs
property (T) and completeness, and no citation.

Completeness of `K_ω` itself is `Analysis/OmegaHilbertComplete`, so the
hypothesis is discharged where the collapse uses it.

## What is still hypothesis, and why

`collapse_contradiction_of_hasKazhdanPropertyT` takes one named hypothesis,
`htransport`: the identification of `Fix π(sLs⁻¹)` with `Fix π(L)`.  The
weighted transport theorem is invoked at `ν_n = k_n` in
`Sofic/CollapseRankWeightTransport`; what is missing between that and
`htransport` is the passage from the transported *commutant* statement to the
equality of fixed subspaces inside `K_ω`.

`collapse_contradiction` keeps the coboundary as a hypothesis too, for the
cases where the primitive is produced some other way.

Separately, applying any of this to `K_ω` still needs the conjugation action
of `Analysis/CollapseCocycleAnalytic.conjQ` bundled as a homomorphism
`L →* (KOmega ≃ₗᵢ[ℂ] KOmega)`.  Its norm-preservation is
`CollapseCocycleAnalytic.norm_mkK_conjBounded`; what remains is the inverse,
the multiplicativity, and the descent of both to the quotient.
-/

namespace GroupApproximation
namespace CollapseDelormeEndpoint

open Filter Matrix Topology
open KazhdanCornerMatrices ScaledKazhdanTransport UltraproductModelConstruction
open RankNormalizedHilbertization KOmegaHilbert
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

/-! ## The join of finitely many idempotents, and its telescoping -/

section RingTelescope

variable {A : Type*} [Ring A]

/-- The printed `r_1 = 1`, `r_i = ∏_{j < i} (1 - x_j)`.

The product is written as a recursion rather than as `∏ j ∈ Finset.range i`
because `A` is *not* assumed commutative and `Finset.prod` needs a
`CommMonoid`.  The recursion fixes the printed order — `j` increasing, the new
factor entering on the right — which is what the telescoping below uses. -/
def partialComplement (x : ℕ → A) : ℕ → A
  | 0 => 1
  | i + 1 => partialComplement x i * (1 - x i)

@[simp] theorem partialComplement_zero (x : ℕ → A) :
    partialComplement x 0 = 1 := rfl

/-- The printed `e_i = r_i - r_{i+1}`, rearranged. -/
theorem partialComplement_succ (x : ℕ → A) (i : ℕ) :
    partialComplement x (i + 1)
      = partialComplement x i - partialComplement x i * x i := by
  simp only [partialComplement]
  rw [mul_sub, mul_one]

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

-- None of the four lemmas below uses the group structure of `L` — only that
-- its elements index the cocycle — so they are stated before `[Group L]`
-- enters, which keeps the `unusedSectionVars` linter satisfied without an
-- `omit`.  The compressed subgroup likewise enters as a plain map `c : L → L`
-- rather than as a monoid endomorphism: nothing here composes `c` with itself
-- or with the group law, and the printed compression `γ ↦ sγs⁻¹` is delivered
-- by hypotheses of the shape `∀ γ, ∃ δ, s γ s⁻¹ = δ`, from which a function is
-- available by choice while a homomorphism is not.
section Coboundary

variable {L : Type*} {V : Type*} [AddCommGroup V] [Module ℂ V]

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
    (c : L → L) (hy : ∀ g : L, β g = y - π g y)
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
theorem collapse_contradiction (π : L → (V ≃ₗ[ℂ] V)) (β : L → V) (c : L → L)
    (hdelorme : ∃ y : V, ∀ g : L, β g = y - π g y)
    (hcompressed : ∀ a : L, β (c a) = 0)
    (htransport : ∀ y : V, (∀ a : L, π (c a) y = y) → ∀ g : L, π g y = y)
    (hne : ∃ g : L, β g ≠ 0) : False := by
  obtain ⟨y, hy⟩ := hdelorme
  obtain ⟨g, hg⟩ := hne
  exact hg (eq_zero_of_compressed_fixed π β y c hy hcompressed (htransport y) g)

end Coboundary

/-! ## Delorme–Guichardet, discharged -/

section ComplexDelorme

variable {L : Type u} [Group L] {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Delorme–Guichardet on a complex Hilbert space.**  Property (T) makes
every affine isometric action of `L` on a complete complex Hilbert space have
a fixed point.

The printed proof cites `\cite[Theorem 2.12.4]{BHV}` for this; it need not.
`Kazhdan/DelormeFixedPoint.exists_fixed_point_of_hasKazhdanPropertyT` proves
it for a complete **real** Hilbert space, and
`Kazhdan/KazhdanComplex.realifyHom` reads a unitary representation as an
orthogonal representation of the underlying real Hilbert space, with the same
norm — so the cocycle, the affine action and the fixed point are literally the
same objects on both sides, and the whole transfer is the `letI` idiom already
used by `IsKazhdanPair.toComplex`. -/
theorem exists_fixed_point_complex [CompleteSpace E]
    (hT : HasKazhdanPropertyT.{u, u} L) (π : L →* (E ≃ₗᵢ[ℂ] E)) {b : L → E}
    (hb : ∀ g h : L, b (g * h) = b g + π g (b h)) :
    ∃ x : E, ∀ g : L, π g x + b g = x := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  obtain ⟨x, hx⟩ :=
    Delorme.exists_fixed_point_of_hasKazhdanPropertyT hT (realifyHom π)
      (fun g h ↦ hb g h)
  exact ⟨x, fun g ↦ hx g⟩

/-- **The coboundary form**, which is the shape the collapse consumes: the
fixed point of the affine action is a primitive for the cocycle,
`β(g) = y - π(g) y`. -/
theorem exists_primitive_of_hasKazhdanPropertyT [CompleteSpace E]
    (hT : HasKazhdanPropertyT.{u, u} L) (π : L →* (E ≃ₗᵢ[ℂ] E)) {β : L → E}
    (hβ : ∀ g h : L, β (g * h) = β g + π g (β h)) :
    ∃ y : E, ∀ g : L, β g = y - π g y := by
  obtain ⟨y, hy⟩ := exists_fixed_point_complex hT π hβ
  refine ⟨y, fun g ↦ ?_⟩
  calc β g = (π g y + β g) - π g y := by abel
    _ = y - π g y := by rw [hy g]

/-- **`CO.21b`, with Delorme–Guichardet discharged.**

The printed last paragraph, from property (T) alone.  `hβ` is the cocycle
identity of the previous step, `hcompressed` is the printed `d_{sas⁻¹} = 0`,
`hne` is the nonvanishing of `β`, and `htransport` is the one remaining
analytic input — the identification of `Fix π(sLs⁻¹)` with `Fix π(L)` that the
weighted transport theorem supplies at `ν_n = k_n`.  The coboundary is no
longer a hypothesis and no longer a citation.

Applied at `E = KOmega Y w ω hw`, whose completeness is
`Analysis/OmegaHilbertComplete`, this is the printed contradiction inside the
rank-normalized ultraproduct. -/
theorem collapse_contradiction_of_hasKazhdanPropertyT [CompleteSpace E]
    (hT : HasKazhdanPropertyT.{u, u} L) (π : L →* (E ≃ₗᵢ[ℂ] E)) (β : L → E)
    (c : L → L)
    (hβ : ∀ g h : L, β (g * h) = β g + π g (β h))
    (hcompressed : ∀ a : L, β (c a) = 0)
    (htransport : ∀ y : E, (∀ a : L, π (c a) y = y) → ∀ g : L, π g y = y)
    (hne : ∃ g : L, β g ≠ 0) : False :=
  collapse_contradiction (fun g ↦ (π g).toLinearEquiv) β c
    (exists_primitive_of_hasKazhdanPropertyT hT π hβ) hcompressed htransport hne

end ComplexDelorme

end

end CollapseDelormeEndpoint
end GroupApproximation
