import GroupApproximation.Analysis.StrictCompressionFromPrinted
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
* `Ψ(0) = qI₃ ≠ 0`, so `Ψ` is not additive — *new*:
  `printed_matrixCompression_zero`, `printed_matrixCompression_zero_ne_zero`,
  and `printed_matrixCompression_not_additive`.
* the restriction of `Ψ` to `GL₃(R)` is an injective group homomorphism —
  `printed_matrixCompressionHom_val` and
  `printed_matrixCompressionHom_injective`.
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
  off `RankTwelveEndpoint.tau_compresses_corner`, and
  `printed_tau_conj_corner_le` in the `Subgroup.map` spelling.
* "the compression `eq:compresses-L` is strict … so `e₁₂(1) ∈ L ∖ τLτ⁻¹`" —
  *new*: `printed_s0_mul_t0_ne_one`,
  `printed_ell_not_mem_tau_conj_corner` and `printed_tau_conj_corner_lt`.
* "`prop:max-infinite`, applied to `L ≤ H` and `τ`, puts a proper isometry in
  `C*_max(H)`" — *new*: `printed_maximalCStar_not_finite_at_H`.
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
`R` quoted from `ArandaCrow` — are outside this printed-equation layer.  The
centre is proved as `BinaryLeavitt.center_eq_bot` and
`BinaryLeavitt.central_units_trivial`; the exact rank-twelve simplicity claim
is proved unconditionally in `RankTwelveSimplicity` by direct root extraction.
The general Preusser upper sandwich is retained only as an optional parallel
formalization route.
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

/-- The repaired prose's computation `Ψ(0) = qI₃`. -/
theorem printed_matrixCompression_zero :
    LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily 0 =
      LeavittFamily.scalarDiagonal (ι := Fin 3) q := by
  simp [LeavittFamily.matrixCompression, q]

/-- The repaired prose's strict inequality `Ψ(0) ≠ 0`. -/
theorem printed_matrixCompression_zero_ne_zero :
    LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily 0 ≠ 0 := by
  rw [printed_matrixCompression_zero]
  intro h
  apply q_ne_zero
  have hval := congrArg
    (fun M : RankTwelve.Cell R => M (0 : Fin 3) (0 : Fin 3)) h
  simpa [LeavittFamily.scalarDiagonal_apply] using hval

/-- The repaired prose's conclusion that `Ψ` is not additive. -/
theorem printed_matrixCompression_not_additive :
    ¬ ∀ M N : RankTwelve.Cell R,
        LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily (M + N) =
          LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily M +
            LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily N := by
  intro hadd
  apply printed_matrixCompression_zero_ne_zero
  have hzero := hadd 0 0
  simp only [zero_add] at hzero
  apply add_left_cancel (a :=
    LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily 0)
  simpa only [add_zero] using hzero.symm

/-- On units, the matrix compression is the underlying matrix of the specific
group homomorphism `matrixCompressionHom`. -/
theorem printed_matrixCompressionHom_val (u : (RankTwelve.Cell R)ˣ) :
    (↑(LeavittFamily.matrixCompressionHom (ι := Fin 3) leavittFamily u) :
        RankTwelve.Cell R) =
      LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily
        (↑u : RankTwelve.Cell R) :=
  leavittFamily.matrixCompressionHom_val u

/-- The repaired prose's injectivity assertion for the group homomorphism on
`GL₃(R)`. -/
theorem printed_matrixCompressionHom_injective :
    Function.Injective
      (LeavittFamily.matrixCompressionHom (ι := Fin 3) leavittFamily) :=
  leavittFamily.matrixCompressionHom_injective

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
17.–19. `Ψ(0) = qI₃ ≠ 0`, hence `Ψ` is not additive;
20.–21. its restriction to units is the injective group homomorphism
    `matrixCompressionHom`;
22. `A ↦ s₀At₀` sends `I₃` to `pI₃`, and `p ≠ 1`, `pI₃ ≠ I₃`, so the
    `qI₃` summand really is needed;
23. `A ↦ diag(A, I₉)` is injective, which is the printed identification of
    `GL₃(R)` with a subgroup of `GL₁₂(R)`;
24. the unit group of `𝔽₂` is trivial. -/
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
  LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily 0 =
      LeavittFamily.scalarDiagonal (ι := Fin 3) q ∧
  LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily 0 ≠ 0 ∧
  (¬ ∀ M N : RankTwelve.Cell R,
      LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily (M + N) =
        LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily M +
          LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily N) ∧
  Function.Injective
    (LeavittFamily.matrixCompressionHom (ι := Fin 3) leavittFamily) ∧
  (∀ u : (RankTwelve.Cell R)ˣ,
      (↑(LeavittFamily.matrixCompressionHom (ι := Fin 3) leavittFamily u) :
          RankTwelve.Cell R) =
        LeavittFamily.matrixCompression (ι := Fin 3) leavittFamily
          (↑u : RankTwelve.Cell R)) ∧
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
    printed_matrixCompression_zero,
    printed_matrixCompression_zero_ne_zero,
    printed_matrixCompression_not_additive,
    printed_matrixCompressionHom_injective,
    printed_matrixCompressionHom_val,
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

/-! ## The strictness of `eq:compresses-L`, and `prop:max-infinite` at `H`

`non_mf_groups_exist.tex`, the closing paragraph of `prop:defect`:

> Finally, the compression `eq:compresses-L` is strict: by
> `eq:corner-conjugation` and `eq:matrix-compression`, every off-diagonal entry
> of a matrix in `τLτ⁻¹` has the form `s₀at₀`, and
> `t₁(s₀at₀)s₁ = 0 ≠ 1 = t₁·1·s₁`, so `e₁₂(1) ∈ L ∖ τLτ⁻¹`.
> `prop:max-infinite`, applied to `L ≤ H` and `τ`, puts a proper isometry in
> `C*_max(H)`.

The printed `e₁₂(1)` is `RankTwelveEndpoint.ell`, and `ell_mem_corner` already
puts it in `L`.  What is proved below is the other half — that it is not in
`τLτ⁻¹` — and then the application of `prop:max-infinite`, which is the carrier
the closing clause of `thm:headline` ("while `C*_max(H)` is not even finite")
was missing. -/

/-- **`t₁(s₀at₀)s₁ = 0 ≠ 1 = t₁·1·s₁`**, in the form the printed strictness
argument uses it: no element of the corner `s₀Rt₀` is the identity of `R`. -/
theorem printed_s0_mul_t0_ne_one (a : R) :
    leavittFamily.s0 * a * leavittFamily.t0 ≠ 1 := by
  intro h
  have hone : leavittFamily.t1 * (leavittFamily.s0 * a * leavittFamily.t0) *
      leavittFamily.s1 = 1 := by
    rw [h, mul_one, leavittFamily.t1_s1]
  have hsplit : leavittFamily.t1 * (leavittFamily.s0 * a * leavittFamily.t0) *
      leavittFamily.s1 =
      leavittFamily.t1 * leavittFamily.s0 * a *
        (leavittFamily.t0 * leavittFamily.s1) := by
    noncomm_ring
  rw [hsplit, leavittFamily.t1_s0, leavittFamily.t0_s1, zero_mul, zero_mul]
    at hone
  exact zero_ne_one hone

/-- The corner embedding of `12 × 12` units is injective: it is the flattening
isomorphism after `RankTwelve.fullCorner`, and that is injective by
`printed_fullCorner_injective`. -/
theorem printed_flatCornerUnits_injective :
    Function.Injective flatCornerUnits := by
  intro u v h
  apply Units.ext
  apply printed_fullCorner_injective
  exact congrArg Units.val (flat12Units.injective h)

/-- **`eq:corner-conjugation` at an arbitrary corner unit.**  The manuscript
prints the identity for the elementary generators; the strictness argument reads
an entry off an arbitrary element of `τLτ⁻¹`, so it needs the same identity for
every unit of the corner.  The proof is the one
`tau_conj_corner_elementaryRoot` runs, with the generator left general. -/
theorem printed_tau_conj_flatCornerUnits (u : (RankTwelve.Cell R)ˣ) :
    printedTauGL * flatCornerUnits u * printedTauGL⁻¹ =
      flatCornerUnits (leavittFamily.matrixCompressionHom u) := by
  have hmapped := congrArg flat12Units (tauUnit_conj_fullCorner u)
  rw [printedTauGL_eq_flat12Units]
  change flat12Units (RankTwelve.tauUnit leavittFamily) *
      flat12Units (fullCornerUnits u) *
      (flat12Units (RankTwelve.tauUnit leavittFamily))⁻¹ =
    flat12Units (fullCornerUnits (leavittFamily.matrixCompressionHom u))
  simpa only [map_mul, map_inv] using hmapped

/-- The same identity read at the level of `H`. -/
theorem printed_tau_conj_cornerEmbedding_val
    (g : BinaryLeavittSteinberg.ElementaryBase 3) :
    ((tau * cornerEmbedding g * tau⁻¹ : H) : (Matrix (Fin 12) (Fin 12) R)ˣ) =
      flatCornerUnits (leavittFamily.matrixCompressionHom
        (g : (RankTwelve.Cell R)ˣ)) := by
  show printedTauGL * flatCornerUnits (g : (RankTwelve.Cell R)ˣ) *
      printedTauGL⁻¹ = _
  exact printed_tau_conj_flatCornerUnits _

/-- **"so `e₁₂(1) ∈ L ∖ τLτ⁻¹`"**, the half that needs proving.

If `ell` were `τγτ⁻¹` with `γ ∈ L`, then writing `γ = cornerEmbedding g` and
conjugating turns the printed `e₁₂(1)` into `Ψ(g)`; injectivity of the corner
embedding makes that an identity of `3 × 3` units, and its `(1,2)` entry says
`1 = s₀·g₁₂·t₀`, which `printed_s0_mul_t0_ne_one` refutes. -/
theorem printed_ell_not_mem_tau_conj_corner :
    ell ∉ corner.map (MulAut.conj tau).toMonoidHom := by
  rintro ⟨γ, hγ, hconj⟩
  rw [← cornerEmbedding_range] at hγ
  obtain ⟨g, rfl⟩ := hγ
  have hH : (tau * cornerEmbedding g * tau⁻¹ : H) = ell := by
    simpa using hconj
  have hunits : flatCornerUnits (leavittFamily.matrixCompressionHom
        (g : (RankTwelve.Cell R)ˣ)) =
      flatCornerUnits (elementaryUnit (1 : Fin 3) 2 (by decide) (1 : R)) := by
    rw [← printed_tau_conj_cornerEmbedding_val g, hH,
      flatCornerUnits_elementaryUnit]
    simp [ell, cornerIndex]
  have hcell : leavittFamily.matrixCompressionHom (g : (RankTwelve.Cell R)ˣ) =
      elementaryUnit (1 : Fin 3) 2 (by decide) (1 : R) :=
    printed_flatCornerUnits_injective hunits
  have hentry : ((leavittFamily.matrixCompressionHom (g : (RankTwelve.Cell R)ˣ) :
        (RankTwelve.Cell R)ˣ) : RankTwelve.Cell R) 1 2 =
      ((elementaryUnit (1 : Fin 3) 2 (by decide) (1 : R) :
        (RankTwelve.Cell R)ˣ) : RankTwelve.Cell R) 1 2 := by
    rw [hcell]
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  -- `g` is a term of the subgroup `ElementaryBase 3`, so reaching its matrix
  -- entry is two coercions, not one: to the unit and then to the matrix.  A
  -- single ascription `(g : RankTwelve.Cell R)` does not chain them.
  refine printed_s0_mul_t0_ne_one
    (((g : (RankTwelve.Cell R)ˣ) : RankTwelve.Cell R) 1 2) ?_
  have hL : ((leavittFamily.matrixCompressionHom (g : (RankTwelve.Cell R)ˣ) :
        (RankTwelve.Cell R)ˣ) : RankTwelve.Cell R) 1 2 =
      leavittFamily.s0 *
        ((g : (RankTwelve.Cell R)ˣ) : RankTwelve.Cell R) 1 2 *
        leavittFamily.t0 := by
    simp [LeavittFamily.matrixCompression_apply, h12]
  have hR : ((elementaryUnit (1 : Fin 3) 2 (by decide) (1 : R) :
        (RankTwelve.Cell R)ˣ) : RankTwelve.Cell R) 1 2 = 1 := by
    simp [elementaryUnit, h12]
  rw [← hL, ← hR]
  exact hentry

/-- **`eq:compresses-L`**, in the `Subgroup.map` spelling
`prop:max-infinite` consumes. -/
theorem printed_tau_conj_corner_le :
    corner.map (MulAut.conj tau).toMonoidHom ≤ corner := by
  rintro x ⟨γ, hγ, rfl⟩
  simpa using tau_compresses_corner γ hγ

/-- **"the compression `eq:compresses-L` is strict"**, `τLτ⁻¹ ⊊ L`. -/
theorem printed_tau_conj_corner_lt :
    corner.map (MulAut.conj tau).toMonoidHom < corner :=
  lt_of_le_of_ne printed_tau_conj_corner_le (by
    intro h
    exact printed_ell_not_mem_tau_conj_corner (by rw [h]; exact ell_mem_corner))

/-- **"`prop:max-infinite`, applied to `L ≤ H` and `τ`, puts a proper isometry
in `C*_max(H)`."**

This is the carrier for the closing clause of `thm:headline`, "while
`C*_max(H)` is not even finite: it contains a proper isometry".  The proper
isometry itself is the first conjunct of
`manuscriptMaximalCStarRemarkFromPrintedHypotheses` at the same arguments; what
is stated here is the printed conclusion drawn from it. -/
theorem printed_maximalCStar_not_finite_at_H :
    ¬ IsDedekindFiniteMonoid (MaximalGroupCStar H) ∧
      ¬ IsStablyFiniteRing (MaximalGroupCStar H) := by
  have hrem :=
    MaximalCStarPrintedHypotheses.manuscriptMaximalCStarRemarkFromPrintedHypotheses
      H corner tau RankTwelveEndpoint.corner_hasKazhdanPropertyT
      printed_tau_conj_corner_lt
  exact ⟨hrem.2.1, hrem.2.2.1⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
