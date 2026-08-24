import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration

/-!
# Section 5 of the manuscript, equation by equation

`non_mf_groups_exist.tex`, `\section{The binary Leavitt self-compression}`.

This module is the printed-fidelity layer for that section.  It contains no new
mathematics: every displayed equation and every prose justification of Section 5
is restated here *as printed*, over the concrete ring `R = L_{𝔽₂}(1,2)` used in
the manuscript, and discharged from the existing development.  The point of the
file is that an auditor can read the section with the paper open and find each
printed formula as a closed Lean statement about the same concrete objects.

## What is printed, and where it comes from

Printed item, then the source it is discharged from.  Items marked "*new*" are
proved in this file because the manuscript prints them as a *reason* rather than
as a displayed equation, and a reason should be checked, not assumed.

* `eq:leavitt`, `tᵢsⱼ = δᵢⱼ`, `s₀t₀ + s₁t₁ = 1` — the `LeavittFamily` fields of
  `UniversalLeavitt.family`, restated on the concrete `R`.
* `eq:pq`, `p + q = 1` — `LeavittFamily.p0_add_p1`.
* `eq:pq`, `t₁qs₁ = 1` — `LeavittFamily.t1_mul_p1_mul_s1`.
* "In particular `q ≠ 0`" — `RankTwelveEndpoint.q_ne_zero`.
* `eq:matrix-compression` — `LeavittFamily.matrixCompression` and its
  `_one`, `_mul`, `_apply`, `_recover` lemmas.
* the printed reasons `qs₀ = 0`, `t₀q = 0` — *new*: `printed_q_mul_s0`,
  `printed_t0_mul_q`.
* `t₀Ψ(A)s₀ = A`, hence injectivity of `Ψ` — *new*:
  `printed_matrixCompression_injective`, off `matrixCompression_recover`.
* "`A ↦ s₀At₀` sends `I₃` to `pI₃`" — *new*:
  `printed_scalarDiagonal_image_of_one`, with `printed_p0_ne_one` and
  `printed_scalarDiagonal_p0_ne_one` showing the `qI₃` term is really needed.
* "identify `GL₃(R)` with the matrices `diag(A, I₉)`" — *new*:
  `printed_fullCorner_injective`.
* `eq:tau`, `XY = YX = I₆` — `RankTwelve.shift_mul_shiftInv`,
  `RankTwelve.shiftInv_mul_shift`.
* `eq:whitehead-factorization` — `RankTwelve.tau_eq_whitehead_product`, with
  `RankTwelveEndpoint.flat12Units_elementary_mem` for the printed remark that
  each block-unipotent factor is a product of elementary `12 × 12` matrices.
* `τ ∈ EL₁₂(R)` — `RankTwelveEndpoint.printedTauGL_mem`.
* `eq:corner-conjugation` — `RankTwelve.tau_fullCorner_tauInv`.
* `Ψ(e_ij(a)) = e_ij(s₀at₀)` —
  `LeavittFamily.matrixCompression_elementaryUnit`, and its group-level form
  `RankTwelveEndpoint.tau_conj_corner_elementaryRoot`.
* `eq:compresses-L`, `τLτ⁻¹ ≤ L` — *new*: `printed_tau_conj_corner_subset`,
  off `RankTwelveEndpoint.tau_compresses_corner`.
* "the unit group of `𝔽₂` is trivial" — *new*: `printed_f2_unit_eq_one`.

Everything is bundled into the two closed propositions
`PrintedLeavittAlgebraEquations` and `PrintedCompressorEquations`, discharged by
`manuscriptPrintedLeavittAlgebraEquations`,
`manuscriptPrintedCompressorEquations` and their conjunction
`manuscriptSectionFiveEquations`.  All three are hypothesis-free.

## What this file does *not* cover

Section 5 ends by pointing forward to the simplicity argument.  The two
statements the manuscript defers to Section 6 — `prop:simple`
(`RankTwelveEndpoint.PropositionSimple`) and the centre computation of
`R` quoted from `ArandaCrow` — are *not* proved in this printed-equation layer.
The latter is now proved separately as `BinaryLeavitt.center_eq_bot` and
`BinaryLeavitt.central_units_trivial` in `Leavitt/BinaryLeavittSimple.lean`;
it still does not supply the missing Preusser normal-subgroup theorem needed
for `prop:simple`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankTwelveEndpoint

/-! ## `eq:leavitt` on the concrete algebra -/

/-- **`eq:leavitt`, first family, in Kronecker form.**  Writing
`s = (s₀, s₁)` and `t = (t₀, t₁)` for the four generators of
`R = L_{𝔽₂}(1,2)`, the printed relation is `tᵢsⱼ = δᵢⱼ`. -/
theorem printed_leavitt_delta (i j : Fin 2) :
    ![leavittFamily.t0, leavittFamily.t1] i *
        ![leavittFamily.s0, leavittFamily.s1] j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp

/-! ## `eq:pq` -/

/-- The printed abbreviation `q = s₁t₁`.  `RankTwelveEndpoint.q` is defined as
the range idempotent `p₁`, which is this product. -/
theorem printed_q_eq : q = leavittFamily.s1 * leavittFamily.t1 := rfl

/-- The printed abbreviation `p = s₀t₀`. -/
theorem printed_p_eq : leavittFamily.p0 = leavittFamily.s0 * leavittFamily.t0 := rfl

/-! ## The printed reasons behind `eq:matrix-compression`

The manuscript justifies multiplicativity and unitality of `Ψ` by the three
relations `qs₀ = 0`, `t₀q = 0` and `t₀s₀ = 1`.  The first two are printed as a
reason rather than as a displayed equation, so they are proved here directly
from `eq:leavitt` instead of being taken on trust. -/

/-- `qs₀ = 0`: printed as the first half of the reason for `eq:matrix-compression`. -/
theorem printed_q_mul_s0 : q * leavittFamily.s0 = 0 := by
  calc
    q * leavittFamily.s0 =
        leavittFamily.s1 * (leavittFamily.t1 * leavittFamily.s0) := by
      rw [printed_q_eq, mul_assoc]
    _ = 0 := by rw [leavittFamily.t1_s0, mul_zero]

/-- `t₀q = 0`: printed as the second half of the reason for
`eq:matrix-compression`. -/
theorem printed_t0_mul_q : leavittFamily.t0 * q = 0 := by
  calc
    leavittFamily.t0 * q =
        (leavittFamily.t0 * leavittFamily.s1) * leavittFamily.t1 := by
      rw [printed_q_eq, ← mul_assoc]
    _ = 0 := by rw [leavittFamily.t0_s1, zero_mul]

/-! ## `eq:matrix-compression` -/

/-- **Injectivity of `Ψ`.**  The manuscript's stated reason is the identity
`t₀Ψ(A)s₀ = A`, and that identity is exactly
`LeavittFamily.matrixCompression_recover`. -/
theorem printed_matrixCompression_injective :
    Function.Injective
      (LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily) := by
  intro M N h
  calc
    M = LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.t0 *
          LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily M *
          LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.s0 :=
      (leavittFamily.matrixCompression_recover M).symm
    _ = LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.t0 *
          LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily N *
          LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.s0 := by
      rw [h]
    _ = N := leavittFamily.matrixCompression_recover N

/-- **The printed reason for the `qI₃` summand.**  The manuscript says that the
term `qI₃` in `eq:matrix-compression` is needed for unitality *because* the map
`A ↦ s₀At₀` sends `I₃` to `pI₃`.  This is that computation. -/
theorem printed_scalarDiagonal_image_of_one :
    LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.s0 * 1 *
        LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.t0 =
      LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.p0 := by
  rw [mul_one, LeavittFamily.scalarDiagonal_mul, printed_p_eq]

/-- `p ≠ 1`, so the previous computation really does obstruct unitality: the
uncorrected map `A ↦ s₀At₀` is not unital. -/
theorem printed_p0_ne_one : leavittFamily.p0 ≠ 1 := by
  intro h
  have hsum : leavittFamily.p0 + leavittFamily.p1 = 1 := leavittFamily.p0_add_p1
  rw [h] at hsum
  have h2 : (1 : R) + leavittFamily.p1 = 1 + 0 := by
    rw [add_zero]
    exact hsum
  exact leavittFamily.p1_ne_zero (add_left_cancel h2)

/-- The matrix form of the previous statement: `pI₃ ≠ I₃`. -/
theorem printed_scalarDiagonal_p0_ne_one :
    LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.p0 ≠ 1 := by
  intro h
  apply printed_p0_ne_one
  have hval := congrArg
    (fun Z : Matrix (Fin 3) (Fin 3) R => Z 0 0) h
  simpa using hval

/-! ## The identification of `M₃(R)` with `diag(A, I₉)` -/

/-- `diag(A, I₃)` determines `A`. -/
theorem printed_halfCorner_injective :
    Function.Injective (RankTwelve.halfCorner (A := R)) := by
  intro M N h
  have hval := congrArg
    (fun Z : RankTwelve.Half R => Z 0 0) h
  simp [RankTwelve.halfCorner] at hval
  exact hval

/-- **The printed identification.**  "We identify `GL₃(R)` with the subgroup of
`GL₁₂(R)` consisting of the matrices `diag(A, I₉)`": the map `A ↦ diag(A, I₉)`
is injective, and it is unital and multiplicative
(`RankTwelve.fullCorner_one`, `RankTwelve.fullCorner_mul`). -/
theorem printed_fullCorner_injective :
    Function.Injective (RankTwelve.fullCorner (A := R)) := by
  intro M N h
  have hval := congrArg
    (fun Z : RankTwelve.Full R => Z 0 0) h
  simp [RankTwelve.fullCorner] at hval
  exact printed_halfCorner_injective hval

/-! ## `eq:compresses-L` -/

/-- **`eq:compresses-L`: `τLτ⁻¹ ≤ L`.**  Conjugation by the printed `τ` carries
the printed corner `L = EL₃(R) ≤ H` into itself. -/
theorem printed_tau_conj_corner_subset :
    (fun g : H => tau * g * tau⁻¹) '' (corner : Set H) ⊆ (corner : Set H) := by
  rintro _ ⟨g, hg, rfl⟩
  exact tau_compresses_corner g hg

/-! ## The prose claim about `𝔽₂` -/

/-- **"The field `𝔽₂` … its unit group is trivial."**  Every unit of `ZMod 2`
is `1`. -/
theorem printed_f2_unit_eq_one (u : (ZMod 2)ˣ) : u = 1 := by
  have key : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hmul : (u : ZMod 2) * (↑u⁻¹ : ZMod 2) = 1 := u.mul_inv
  refine Units.ext ?_
  rcases key (u : ZMod 2) with h | h
  · rw [h, zero_mul] at hmul
    exact absurd hmul (by decide)
  · simp [h]

/-- The same statement as a `Subsingleton`. -/
theorem printed_f2_units_subsingleton : Subsingleton (ZMod 2)ˣ :=
  ⟨fun a b => by rw [printed_f2_unit_eq_one a, printed_f2_unit_eq_one b]⟩

/-! ## The two printed bundles -/

/-- **Section 5, ring-and-matrix layer, verbatim.**

Conjuncts in printed order:

1. `eq:leavitt`, `tᵢsⱼ = δᵢⱼ`;
2. `eq:leavitt`, `s₀t₀ + s₁t₁ = 1`;
3. the abbreviation `p = s₀t₀`;
4. the abbreviation `q = s₁t₁`;
5. `eq:pq`, `p + q = 1`;
6. `eq:pq`, `t₁qs₁ = 1`;
7. "In particular `q ≠ 0`";
8. `eq:matrix-compression`, `Ψ(A) = qI₃ + s₀At₀`;
9. the entrywise reading `s₀At₀ = (s₀a_{ij}t₀)_{ij}`;
10.–12. the printed reasons `qs₀ = 0`, `t₀q = 0`, `t₀s₀ = 1`;
13. `Ψ` is unital;
14. `Ψ` is multiplicative;
15. `t₀Ψ(A)s₀ = A`;
16. `Ψ` is injective;
17. `A ↦ s₀At₀` sends `I₃` to `pI₃`, and (18.–19.) `p ≠ 1`, `pI₃ ≠ I₃`, so the
    `qI₃` summand really is needed;
20. `A ↦ diag(A, I₉)` is injective, which is the printed identification of
    `GL₃(R)` with a subgroup of `GL₁₂(R)`;
21. the unit group of `𝔽₂` is trivial. -/
def PrintedLeavittAlgebraEquations : Prop :=
  (∀ i j : Fin 2,
      ![leavittFamily.t0, leavittFamily.t1] i *
        ![leavittFamily.s0, leavittFamily.s1] j = if i = j then 1 else 0) ∧
  leavittFamily.s0 * leavittFamily.t0 + leavittFamily.s1 * leavittFamily.t1 = 1 ∧
  leavittFamily.p0 = leavittFamily.s0 * leavittFamily.t0 ∧
  q = leavittFamily.s1 * leavittFamily.t1 ∧
  leavittFamily.p0 + q = 1 ∧
  leavittFamily.t1 * q * leavittFamily.s1 = 1 ∧
  q ≠ 0 ∧
  (∀ M : RankTwelve.Cell R,
      LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily M =
        LeavittFamily.scalarDiagonal (ι := Fin 3) q +
          LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.s0 * M *
            LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.t0) ∧
  (∀ (M : RankTwelve.Cell R) (i j : Fin 3),
      LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily M i j =
        (if i = j then q else 0) + leavittFamily.s0 * M i j * leavittFamily.t0) ∧
  q * leavittFamily.s0 = 0 ∧
  leavittFamily.t0 * q = 0 ∧
  leavittFamily.t0 * leavittFamily.s0 = 1 ∧
  LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily 1 = 1 ∧
  (∀ M N : RankTwelve.Cell R,
      LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily (M * N) =
        LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily M *
          LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily N) ∧
  (∀ M : RankTwelve.Cell R,
      LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.t0 *
          LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily M *
          LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.s0 = M) ∧
  Function.Injective
    (LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily) ∧
  (LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.s0 * 1 *
      LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.t0 =
    LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.p0) ∧
  leavittFamily.p0 ≠ 1 ∧
  LeavittFamily.scalarDiagonal (ι := Fin 3) leavittFamily.p0 ≠ 1 ∧
  Function.Injective (RankTwelve.fullCorner (A := R)) ∧
  (∀ u : (ZMod 2)ˣ, u = 1)

/-- **Section 5, ring-and-matrix layer, discharged.** -/
theorem manuscriptPrintedLeavittAlgebraEquations :
    PrintedLeavittAlgebraEquations :=
  ⟨printed_leavitt_delta,
    leavittFamily.sum_range,
    printed_p_eq,
    printed_q_eq,
    leavittFamily.p0_add_p1,
    leavittFamily.t1_mul_p1_mul_s1,
    q_ne_zero,
    fun _ => rfl,
    fun M i j => leavittFamily.matrixCompression_apply M i j,
    printed_q_mul_s0,
    printed_t0_mul_q,
    leavittFamily.t0_s0,
    leavittFamily.matrixCompression_one,
    fun M N => leavittFamily.matrixCompression_mul M N,
    fun M => leavittFamily.matrixCompression_recover M,
    printed_matrixCompression_injective,
    printed_scalarDiagonal_image_of_one,
    printed_p0_ne_one,
    printed_scalarDiagonal_p0_ne_one,
    printed_fullCorner_injective,
    printed_f2_unit_eq_one⟩

/-- **Section 5, compressor layer, verbatim.**

Conjuncts in printed order:

1.–2. the displayed matrices `X` and `Y`;
3.–4. "a direct calculation using `eq:leavitt` gives `XY = YX = I₆`";
5. `eq:tau`, `τ = diag(X, Y)`;
6. "since `Y = X⁻¹`" — the printed `Y` really is the inverse of the printed `X`;
7. `τ ∈ GL₁₂(R)`, the containment asserted by `eq:tau`;
8. `eq:whitehead-factorization`, all six printed factors;
9. "each block-unipotent factor is a product of elementary `12 × 12` matrices";
10. `τ ∈ EL₁₂(R)`;
11. `eq:corner-conjugation`, `τ diag(A, I₉) τ⁻¹ = diag(Ψ(A), I₉)`;
12. "for every `i ≠ j` and `a ∈ R`, `Ψ(e_ij(a)) = e_ij(s₀at₀)`";
13. the same identity inside the group `H`, for the printed corner `L`;
14. `eq:compresses-L`, `τLτ⁻¹ ≤ L`. -/
def PrintedCompressorEquations : Prop :=
  RankTwelve.shift leavittFamily =
      !![RankTwelve.kap leavittFamily.s0,
          RankTwelve.kap (leavittFamily.s1 * leavittFamily.t0);
        0, RankTwelve.kap leavittFamily.t1] ∧
  RankTwelve.shiftInv leavittFamily =
      !![RankTwelve.kap leavittFamily.t0, 0;
        RankTwelve.kap (leavittFamily.s0 * leavittFamily.t1),
          RankTwelve.kap leavittFamily.s1] ∧
  RankTwelve.shift leavittFamily * RankTwelve.shiftInv leavittFamily = 1 ∧
  RankTwelve.shiftInv leavittFamily * RankTwelve.shift leavittFamily = 1 ∧
  RankTwelve.tau leavittFamily =
      !![RankTwelve.shift leavittFamily, 0; 0, RankTwelve.shiftInv leavittFamily] ∧
  ((RankTwelve.shiftUnit leavittFamily)⁻¹ : (RankTwelve.Half R)ˣ).val =
      RankTwelve.shiftInv leavittFamily ∧
  IsUnit (RankTwelve.tau leavittFamily) ∧
  (RankTwelve.tau leavittFamily =
      RankTwelve.upperBlock (RankTwelve.shift leavittFamily) *
        RankTwelve.lowerBlock (-RankTwelve.shiftInv leavittFamily) *
        RankTwelve.upperBlock (RankTwelve.shift leavittFamily) *
        RankTwelve.lowerBlock 1 * RankTwelve.upperBlock (-1) *
        RankTwelve.lowerBlock 1) ∧
  (∀ (b c : Fin 2) (hbc : b ≠ c) (Z : RankTwelve.Half R),
      flat12Units (elementaryUnit b c hbc Z) ∈ elementaryGroup (Fin 12) R) ∧
  printedTauGL ∈ elementaryGroup (Fin 12) R ∧
  (∀ M : RankTwelve.Cell R,
      RankTwelve.tau leavittFamily * RankTwelve.fullCorner M *
          RankTwelve.tauInv leavittFamily =
        RankTwelve.fullCorner
          (LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily M)) ∧
  (∀ (i j : Fin 3) (hij : i ≠ j) (a : R),
      LeavittFamily.matrixCompressionHom (ι := Fin 3) leavittFamily
          (elementaryUnit i j hij a) =
        elementaryUnit i j hij (leavittFamily.s0 * a * leavittFamily.t0)) ∧
  (∀ (i j : Fin 3) (hij : i ≠ j) (a : R),
      tau * elementaryRoot (cornerIndex i) (cornerIndex j)
          (cornerIndex_injective.ne hij) a * tau⁻¹ =
        elementaryRoot (cornerIndex i) (cornerIndex j)
          (cornerIndex_injective.ne hij)
          (leavittFamily.s0 * a * leavittFamily.t0)) ∧
  (fun g : H => tau * g * tau⁻¹) '' (corner : Set H) ⊆ (corner : Set H)

/-- **Section 5, compressor layer, discharged.** -/
theorem manuscriptPrintedCompressorEquations : PrintedCompressorEquations :=
  ⟨rfl,
    rfl,
    RankTwelve.shift_mul_shiftInv leavittFamily,
    RankTwelve.shiftInv_mul_shift leavittFamily,
    rfl,
    RankTwelve.shiftUnit_inv_val leavittFamily,
    ⟨RankTwelve.tauUnit leavittFamily, rfl⟩,
    RankTwelve.tau_eq_whitehead_product leavittFamily,
    fun b c hbc Z => flat12Units_elementary_mem b c hbc Z,
    printedTauGL_mem,
    RankTwelve.tau_fullCorner_tauInv leavittFamily,
    fun i j hij a => leavittFamily.matrixCompression_elementaryUnit i j hij a,
    fun i j hij a => tau_conj_corner_elementaryRoot i j hij a,
    printed_tau_conj_corner_subset⟩

/-- **Everything Section 5 prints, in one hypothesis-free statement.** -/
theorem manuscriptSectionFiveEquations :
    PrintedLeavittAlgebraEquations ∧ PrintedCompressorEquations :=
  ⟨manuscriptPrintedLeavittAlgebraEquations,
    manuscriptPrintedCompressorEquations⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
