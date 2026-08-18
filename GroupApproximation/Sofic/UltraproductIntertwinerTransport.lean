import GroupApproximation.Sofic.IntertwinerKazhdanTransport

/-!
# Ultraproduct Kazhdan transport of asymptotic intertwiners

This file proves the intertwiner transport variant by the block reduction
feeding the **ultraproduct** proof of `thm:kazhdan-transport`.  **The printed
clause was cut from the manuscript on 2026-08-18**: `thm:transport-variants`
now states the weighted variant alone, and neither the intertwiner statement
nor its six-step proof is printed any more (see the change-history table of
`docs/NON_MF_PROOF_LEDGER.md`); no badge is owed for this module.

The six steps below record the formal argument as it stood when it mirrored
the print, and the declarations keep their step names.

```
IT.01  it_01_blockSum_defect_eq_max            W_n = U¹_n ⊕ U²_n is an operator-norm
       it_01_blockSum_asymptotically_multiplicative
                                               asymptotic representation, because
                                               block-diagonal operator norms are maxima.
IT.02  it_02_opNorm_offDiagBlock                the off-diagonal embedding of x_n into the
                                               block space has operator norm ‖x_n‖.
IT.03  it_03_defect_is_offDiagBlock             the commutator of the embedded corner with
       it_03_hsNormSq_defect_eq                 W_n(ι γ) is the off-diagonal embedding of the
                                               intertwining defect, and the normalized
                                               Hilbert--Schmidt norm on the block space
                                               carries exactly the denominator d¹_n + d²_n.
IT.04  it_04_blockConjugation_on_corner         conjugation by W_n(s) acts on the embedded
                                               corner by x_n ↦ U¹_n(s) x_n U²_n(s)*.
IT.05  it_05_intertwiner_transport              apply `thm:kazhdan-transport` — the
                                               ultraproduct proof — to W_n, transporting the
                                               embedded sequence.
IT.06  it_06_scaled_intertwiner_transport       the same reduction through part (1) gives the
                                               intertwiner transport at every weight.
```

## STATUS — READ BEFORE CITING ANYTHING BELOW

**Steps IT.01--IT.04 are CLOSED.**  They are unconditional theorems with
complete proofs, they assume nothing from any other module, and they are the
whole mathematical content of the manuscript's block reduction.

**Steps IT.05 and IT.06 are NOT CLOSED, and neither are the two endpoints
`manuscriptUltraproductIntertwinerTransport` and
`scaled_ultraproduct_intertwiner_transport`.**  Each of the four takes the
transport theorem it needs as an explicit hypothesis
(`UltraproductTransportFor` / `UltraproductScaledTransportFor`) rather than
proving it.  What is genuinely established there is only the *reduction*:
that the rectangular statement follows from the square one.  **None of these
four may carry a `\leanverified` badge**, because none of them proves
`thm:transport-variants`(2) outright.

The hypotheses are not vacuous — `UltraproductTransportFor Γ E` is exactly
the statement of `KazhdanAsymptoticCommutant.transport` and
`UltraproductScaledTransportFor Γ E` exactly that of
`ScaledKazhdanTransport.scaled_transport`, both of which are proved
unconditionally in this repository — so the reductions below do have
content.  But discharging them *that* way yields the finite-stage route of
Appendix `app:finite-stage`, which
`Sofic/IntertwinerKazhdanTransport.lean` already certifies.  Closing IT.05
and IT.06 *as the printed proof* requires the ultraproduct route, and that
is not available yet.

This file deliberately does **not** mention `UltraproductAdjointModel` or
`WeightedUltraproductAdjointModel`, so no unconstructed bundling structure
leaks into the block reduction.

The block bookkeeping (`offDiagBlock`, `rectMass`, `blockSumRep`, and the
corner/commutant dictionary) is route-neutral and is reused verbatim from
`Sofic.IntertwinerKazhdanTransport`, so that the ultraproduct route and the
finite-stage route of that file prove *literally the same statements*.  Only
the transport invocation differs.
-/

namespace GroupApproximation
namespace UltraproductIntertwinerTransport

open Matrix KazhdanCornerMatrices KazhdanAsymptoticCommutant
open ScaledKazhdanTransport IntertwinerKazhdanTransport
open scoped Matrix.Norms.L2Operator

/-! ## The interface to the ultraproduct proof of `thm:kazhdan-transport` -/

/-- **The IT.05 input — an UNPROVED hypothesis, not a theorem of this file.**
The conclusion of the manuscript's `thm:kazhdan-transport` for the ambient
group `E` and the Kazhdan source `Γ`: a one-sided compressor of a Kazhdan
image preserves every uniformly operator-norm-bounded normalized
Hilbert--Schmidt asymptotic commutant.

This is the statement whose *printed* proof, inside `\ref{sec:transport}`, is
the ultraproduct argument: the adjoint model, the norm ultraproduct `B_ω`, the
projection onto the fixed subspace, the agreement of the two projections, and
the conclusion.

It is word-for-word the statement of `KazhdanAsymptoticCommutant.transport`,
which this repository proves unconditionally by the *finite-stage* route (a
Lean-only route since commit `3a45fa60` cut the appendix that printed it).  So
the hypothesis is satisfiable and anything
assuming it is non-vacuous — but satisfying it that way reproves the
alternate route already certified in
`Sofic/IntertwinerKazhdanTransport.lean`, not the printed one. -/
abbrev UltraproductTransportFor (Γ E : Type) [Group Γ] [Group E] : Prop :=
  ∀ (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ),
    IsAsymptoticCommutant B C x → IsUniformlyBounded B x →
    IsAsymptoticCommutant B C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ)

/-- **The IT.06 input — an UNPROVED hypothesis, not a theorem of this file.**
Part (1) of `\ref{thm:transport-variants}`: the same transport at an arbitrary
nonnegative Hilbertian weight `w`, again by the ultraproduct argument --- "the
ultraproduct proof of Theorem `\ref{thm:kazhdan-transport}` applies with
`\tr_{d_n}` replaced by `\operatorname{Tr}(\,\cdot\,)/\nu_n`", in the printed
proof of part (1).

As with the unweighted input, this is word-for-word the statement of
`ScaledKazhdanTransport.scaled_transport`, proved unconditionally here by the
finite-stage route; satisfiable, therefore, but not by the printed proof. -/
abbrev UltraproductScaledTransportFor (Γ E : Type) [Group Γ] [Group E] :
    Prop :=
  ∀ (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (_hw : ∀ n, 0 ≤ w n)
    (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ),
    IsScaledAsymptoticCommutant B w C x → IsScaledMassBounded B w x →
    IsScaledAsymptoticCommutant B w C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ)

section BlockReduction

variable {Γ E : Type} [Group Γ] [Group E]

/-! ## IT.01 — the block sum is an operator-norm asymptotic representation -/

/-- **IT.01, the reason.**  The multiplicative defect of the block sum
`W_n = U¹_n ⊕ U²_n` at a pair `(g, h)` is the *maximum* of the two defects,
because block-diagonal operator norms are maxima. -/
theorem it_01_blockSum_defect_eq_max (B₁ B₂ : OpAlmostRepresentation E)
    (n : ℕ) (g h : E) :
    ‖blockDiagMatrix (B₁.model n) (B₂.model n)
          (B₁.map n (g * h)) (B₂.map n (g * h)) -
        blockDiagMatrix (B₁.model n) (B₂.model n)
            (B₁.map n g) (B₂.map n g) *
          blockDiagMatrix (B₁.model n) (B₂.model n)
            (B₁.map n h) (B₂.map n h)‖ =
      max ‖(B₁.map n (g * h) : Matrix (B₁.model n) (B₁.model n) ℂ) -
            (B₁.map n g : Matrix (B₁.model n) (B₁.model n) ℂ) * B₁.map n h‖
        ‖(B₂.map n (g * h) : Matrix (B₂.model n) (B₂.model n) ℂ) -
            (B₂.map n g : Matrix (B₂.model n) (B₂.model n) ℂ) *
              B₂.map n h‖ := by
  rw [blockDiagMatrix_mul, blockDiagMatrix_sub, l2_opNorm_blockDiag]

/-- **IT.01.**  Consequently the block sum `W_n = U¹_n ⊕ U²_n` is itself an
operator-norm asymptotic representation of the ambient group; it is the
almost representation `blockSumRep B₁ B₂`. -/
theorem it_01_blockSum_asymptotically_multiplicative
    (B₁ B₂ : OpAlmostRepresentation E) (g h : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N,
      ‖blockDiagMatrix (B₁.model n) (B₂.model n)
            (B₁.map n (g * h)) (B₂.map n (g * h)) -
          blockDiagMatrix (B₁.model n) (B₂.model n)
              (B₁.map n g) (B₂.map n g) *
            blockDiagMatrix (B₁.model n) (B₂.model n)
              (B₁.map n h) (B₂.map n h)‖ ≤ ε :=
  (blockSumRep B₁ B₂).asymptoticallyMultiplicative g h ε hε

/-! ## IT.02 — the off-diagonal embedding is isometric for the operator norm -/

/-- **IT.02.**  The off-diagonal embedding of a rectangular matrix into the
block space has operator norm exactly `‖x_n‖`.

The inequality `≤` is `l2_opNorm_offDiagBlock_le`; the reverse inequality
tests the embedded matrix on the vectors supported in the second summand,
where the embedded corner reproduces `X` exactly. -/
theorem it_02_opNorm_offDiagBlock (Y Z : FiniteModel) (X : Matrix Y Z ℂ) :
    ‖offDiagBlock Y Z X‖ = ‖X‖ := by
  classical
  refine le_antisymm (l2_opNorm_offDiagBlock_le Y Z X) ?_
  set F : Matrix (blockSumModel Y Z) (blockSumModel Y Z) ℂ :=
    offDiagBlock Y Z X with hF
  have hmv : ∀ v : (Y ⊕ Z) → ℂ,
      F *ᵥ v = Sum.elim (X *ᵥ (v ∘ Sum.inr)) 0 := by
    intro v
    rw [hF]
    unfold offDiagBlock
    rw [Matrix.fromBlocks_mulVec]
    congr 1 <;> simp
  refine l2_opNorm_le_of_sum_normSq_general X (norm_nonneg F) fun x ↦ ?_
  set xhat : (Y ⊕ Z) → ℂ := Sum.elim 0 x with hxhat
  have hcomp : xhat ∘ Sum.inr = x := rfl
  have hval : ∀ i : Y, (X *ᵥ x) i = (F *ᵥ xhat) (Sum.inl i) := by
    intro i
    rw [hmv, hcomp]
    rfl
  have hxsum : ∑ p : Y ⊕ Z, Complex.normSq (xhat p) =
      ∑ j : Z, Complex.normSq (x j) := by
    rw [Fintype.sum_sum_type]
    simp [hxhat]
  calc
    ∑ i : Y, Complex.normSq ((X *ᵥ x) i) =
        ∑ i : Y, Complex.normSq ((F *ᵥ xhat) (Sum.inl i)) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [hval i]
    _ ≤ ∑ p : Y ⊕ Z, Complex.normSq ((F *ᵥ xhat) p) := by
      rw [Fintype.sum_sum_type]
      exact le_add_of_nonneg_right
        (Finset.sum_nonneg fun j _ ↦ Complex.normSq_nonneg _)
    _ ≤ ‖F‖ ^ 2 * ∑ p : Y ⊕ Z, Complex.normSq (xhat p) :=
      sum_normSq_mulVec_le (blockSumModel Y Z) F xhat
    _ = ‖F‖ ^ 2 * ∑ j : Z, Complex.normSq (x j) := by rw [hxsum]

/-- **IT.02, in the form the transport theorem consumes.**  A uniformly
operator-norm-bounded rectangular sequence embeds to a uniformly
operator-norm-bounded sequence on the block space, with the same bound. -/
theorem it_02_isUniformlyBounded_offDiagBlock
    (B₁ B₂ : OpAlmostRepresentation E)
    {x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ}
    (hx : IsUniformlyBoundedRect B₁ B₂ x) :
    IsUniformlyBounded (blockSumRep B₁ B₂)
      (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n) (x n)) :=
  isUniformlyBounded_offDiag B₁ B₂ hx

/-! ## IT.03 — the commutator is the embedded intertwining defect -/

/-- **IT.03, first half.**  The invariance defect of the embedded corner
under `W_n(ι γ)` is the off-diagonal embedding of the *rectangular*
intertwining defect `X - U¹_n(ι γ) X U²_n(ι γ)*`. -/
theorem it_03_defect_is_offDiagBlock (Y Z : FiniteModel)
    (U : Matrix Y Y ℂ) (V : Matrix Z Z ℂ) (X : Matrix Y Z ℂ) :
    offDiagBlock Y Z X -
        blockDiagMatrix Y Z U V * offDiagBlock Y Z X *
          (blockDiagMatrix Y Z U V)ᴴ =
      offDiagBlock Y Z (X - U * X * Vᴴ) := by
  rw [blockDiag_conj_offDiag, offDiagBlock_sub]

/-- **IT.03, second half.**  The normalized Hilbert--Schmidt norm on the
block space carries exactly the denominator `d¹_n + d²_n`: the normalized
squared norm of the embedded defect is the unnormalized rectangular mass of
the defect divided by `card Y + card Z`.  This is where the denominator in
the hypothesis of part (2) comes from. -/
theorem it_03_hsNormSq_defect_eq (Y Z : FiniteModel)
    (U : Matrix Y Y ℂ) (V : Matrix Z Z ℂ) (X : Matrix Y Z ℂ) :
    hsNormSq (blockSumModel Y Z)
        (offDiagBlock Y Z X -
          blockDiagMatrix Y Z U V * offDiagBlock Y Z X *
            (blockDiagMatrix Y Z U V)ᴴ) =
      rectMass (X - U * X * Vᴴ) /
        ((Fintype.card Y : ℝ) + Fintype.card Z) := by
  rw [it_03_defect_is_offDiagBlock, hsNormSq_offDiagBlock]

/-- **IT.03, packaged.**  Consequently the block-normalized asymptotic
intertwiners between `B₁|Γ` and `B₂|Γ` are exactly the normalized
Hilbert--Schmidt asymptotic commutants of the block sum that are supported
on the embedded corner. -/
theorem it_03_commutant_iff_intertwiner (B₁ B₂ : OpAlmostRepresentation E)
    (iota : Γ →* E) (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ) :
    IsAsymptoticCommutantOf (blockSumRep B₁ B₂) iota
        (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n) (x n)) ↔
      IsAsymptoticIntertwinerOf B₁ B₂ iota x :=
  isAsymptoticCommutantOf_offDiag_iff B₁ B₂ iota x

/-! ## IT.04 — conjugation by the block compressor acts on the corner -/

/-- **IT.04.**  Conjugation by `W_n(s)` acts on the embedded corner by
`x_n ↦ U¹_n(s) x_n U²_n(s)*`. -/
theorem it_04_blockConjugation_on_corner (B₁ B₂ : OpAlmostRepresentation E)
    (n : ℕ) (g : E) (X : Matrix (B₁.model n) (B₂.model n) ℂ) :
    ((blockSumRep B₁ B₂).map n g :
        Matrix (blockSumModel (B₁.model n) (B₂.model n))
          (blockSumModel (B₁.model n) (B₂.model n)) ℂ) *
        offDiagBlock (B₁.model n) (B₂.model n) X *
        ((blockSumRep B₁ B₂).map n g :
          Matrix (blockSumModel (B₁.model n) (B₂.model n))
            (blockSumModel (B₁.model n) (B₂.model n)) ℂ)ᴴ =
      offDiagBlock (B₁.model n) (B₂.model n)
        ((B₁.map n g : Matrix (B₁.model n) (B₁.model n) ℂ) * X *
          (B₂.map n g : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) := by
  rw [blockSumRep_map_coe, blockDiag_conj_offDiag]

/-! ## IT.05 — apply the ultraproduct transport to the block sum -/

/-- **IT.05 — NOT CLOSED.  This is a reduction, not a proof of the step.**

What is proved: *if* `thm:kazhdan-transport` holds (hypothesis `hUP`), then
applying it to the block sum `W_n` and reading the corner back off gives the
transport of asymptotic intertwiners.  The reduction itself is complete and
rests only on the closed steps IT.01--IT.04.

What is *not* proved: `hUP`.  The manuscript discharges it by the
ultraproduct argument printed under `\ref{thm:kazhdan-transport}` in
`\ref{sec:transport}`, which is not yet available in this
repository.  Until it is, this declaration does not certify
`\ref{thm:transport-variants}`(2) and must not be badged. -/
theorem it_05_intertwiner_transport
    (hUP : UltraproductTransportFor Γ E)
    (B₁ B₂ : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ)
    (hx : IsAsymptoticIntertwiner B₁ B₂ C x)
    (hbound : IsUniformlyBoundedRect B₁ B₂ x) :
    IsAsymptoticIntertwiner B₁ B₂ C (fun n ↦
      (B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
        (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) := by
  have hcomm := (it_03_commutant_iff_intertwiner B₁ B₂ C.iota x).mpr hx
  have htrans := hUP (blockSumRep B₁ B₂) C
    (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n) (x n)) hcomm
    (it_02_isUniformlyBounded_offDiagBlock B₁ B₂ hbound)
  have hz : ∀ n : ℕ,
      ((blockSumRep B₁ B₂).map n C.t :
          Matrix (blockSumModel (B₁.model n) (B₂.model n))
            (blockSumModel (B₁.model n) (B₂.model n)) ℂ) *
          offDiagBlock (B₁.model n) (B₂.model n) (x n) *
          ((blockSumRep B₁ B₂).map n C.t :
            Matrix (blockSumModel (B₁.model n) (B₂.model n))
              (blockSumModel (B₁.model n) (B₂.model n)) ℂ)ᴴ =
        offDiagBlock (B₁.model n) (B₂.model n)
          ((B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
            (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) :=
    fun n ↦ it_04_blockConjugation_on_corner B₁ B₂ n C.t (x n)
  have hcomm' : IsAsymptoticCommutantOf (blockSumRep B₁ B₂) C.iota
      (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n)
        ((B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
          (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ)) := by
    intro γ
    exact (htrans γ).congr fun n ↦ by simp only [hz]
  exact (it_03_commutant_iff_intertwiner B₁ B₂ C.iota _).mp hcomm'

/-! ## IT.06 — the same reduction through part (1), at every weight -/

/-- **IT.06 — NOT CLOSED.  This is a reduction, not a proof of the step.**

What is proved: the block reduction is weight-blind, so *if* part (1) of
`thm:transport-variants` holds (hypothesis `hUPs`), running IT.01--IT.04
against it transports asymptotic intertwiners at every nonnegative weight.

What is *not* proved: `hUPs`.  Same situation as IT.05, at every weight.
Not to be badged. -/
theorem it_06_scaled_intertwiner_transport
    (hUPs : UltraproductScaledTransportFor Γ E)
    (B₁ B₂ : OpAlmostRepresentation E) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ)
    (hx : IsScaledAsymptoticIntertwinerOf B₁ B₂ w C.iota x)
    (hbound : IsScaledRectMassBounded B₁ B₂ w x) :
    IsScaledAsymptoticIntertwinerOf B₁ B₂ w C.iota (fun n ↦
      (B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
        (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) := by
  have hcomm :=
    (isScaledAsymptoticCommutantOf_offDiag_iff B₁ B₂ w C.iota x).mpr hx
  have htrans := hUPs (blockSumRep B₁ B₂) w hw C
    (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n) (x n)) hcomm
    (isScaledMassBounded_offDiag B₁ B₂ w hbound)
  have hz : ∀ n : ℕ,
      ((blockSumRep B₁ B₂).map n C.t :
          Matrix (blockSumModel (B₁.model n) (B₂.model n))
            (blockSumModel (B₁.model n) (B₂.model n)) ℂ) *
          offDiagBlock (B₁.model n) (B₂.model n) (x n) *
          ((blockSumRep B₁ B₂).map n C.t :
            Matrix (blockSumModel (B₁.model n) (B₂.model n))
              (blockSumModel (B₁.model n) (B₂.model n)) ℂ)ᴴ =
        offDiagBlock (B₁.model n) (B₂.model n)
          ((B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
            (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) :=
    fun n ↦ it_04_blockConjugation_on_corner B₁ B₂ n C.t (x n)
  have hcomm' : IsScaledAsymptoticCommutantOf (blockSumRep B₁ B₂) w C.iota
      (fun n ↦ offDiagBlock (B₁.model n) (B₂.model n)
        ((B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
          (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ)) := by
    intro γ
    exact (htrans γ).congr fun n ↦ by simp only [hz]
  exact
    (isScaledAsymptoticCommutantOf_offDiag_iff B₁ B₂ w C.iota _).mp hcomm'

end BlockReduction

/-! ## The manuscript endpoints -/

universe uK

/-- **`thm:transport-variants`(2), in the exact manuscript coordinates, by
the ultraproduct route — NOT CLOSED.  Do not badge this declaration.**

It carries the hypothesis `_hUP`, the unproved statement of
`thm:kazhdan-transport`; see the STATUS block at the head of this file.  What
is established is the manuscript's block reduction (IT.01--IT.05) in the
literal `M_{d¹_n × d²_n}` coordinates, i.e. that part (2) follows from
`thm:kazhdan-transport`.  The statement is otherwise identical to
`IntertwinerKazhdanTransport.manuscriptIntertwinerTransport`, which *is*
closed, by the finite-stage route.

Let `U¹_n : H → U(d¹_n)` and `U²_n : H → U(d²_n)` be operator-norm
asymptotic representations, let `s ι(Γ) s⁻¹ ⊆ ι(Γ)` with `Γ` Kazhdan, and
let `(x_n)` be uniformly operator-norm bounded `d¹_n × d²_n` matrices whose
rectangular intertwining defect satisfies

  `Tr |x_n - U¹_n(ι γ) x_n U²_n(ι γ)*|² / (d¹_n + d²_n) → 0`   for every `γ`.

Then `U¹_n(s) x_n U²_n(s)*` satisfies the same convergence for every `γ`.

The proof is the printed block reduction IT.01--IT.05: the block sum
`W_n = U¹_n ⊕ U²_n` is an operator-norm asymptotic representation, `x_n`
embeds isometrically as an off-diagonal corner whose block-normalized
Hilbert--Schmidt defect is the hypothesis with its `d¹_n + d²_n`
denominator, conjugation by `W_n(s)` acts on the corner by the asserted
formula, and `thm:kazhdan-transport` — by its printed ultraproduct proof,
supplied as `hUP` — transports the embedded sequence. -/
theorem manuscriptUltraproductIntertwinerTransport :
    ∀ {Γ H : Type} [Group Γ] [Group H]
    (_hUP : UltraproductTransportFor Γ H)
    (_hT : HasKazhdanPropertyTComplex.{0, uK} Γ)
    (iota : Γ →* H) (s : H)
    (_hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (d₁ d₂ : ℕ → ℕ) (_hd₁ : ∀ n, 0 < d₁ n) (_hd₂ : ∀ n, 0 < d₂ n)
    (U₁ : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d₁ n)) ℂ)
    (U₂ : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d₂ n)) ℂ)
    (_hU₁ : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U₁ n (g * h) : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) -
        (U₁ n g : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) * U₁ n h‖ ≤ ε)
    (_hU₂ : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U₂ n (g * h) : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ) -
        (U₂ n g : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ) * U₂ n h‖ ≤ ε)
    (x : ∀ n, Matrix (naturalFiniteModel (d₁ n))
      (naturalFiniteModel (d₂ n)) ℂ)
    (_hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
    (_hx : ∀ γ : Γ, NaturalHSIntertwinerVanishing d₁ d₂ U₁ U₂ x (iota γ)),
    ∀ γ : Γ, NaturalHSIntertwinerVanishing d₁ d₂ U₁ U₂
      (fun n ↦ (U₁ n s : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) * x n *
        (U₂ n s : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ)ᴴ) (iota γ) := by
  intro Γ H _ _ hUP hT iota s hs d₁ d₂ hd₁ hd₂ U₁ U₂ hU₁ hU₂ x hbound hx
  let B₁ : OpAlmostRepresentation H := {
    model := fun n ↦ naturalFiniteModel (d₁ n)
    modelNonempty := fun n ↦ by simpa using hd₁ n
    map := U₁
    asymptoticallyMultiplicative := hU₁ }
  let B₂ : OpAlmostRepresentation H := {
    model := fun n ↦ naturalFiniteModel (d₂ n)
    modelNonempty := fun n ↦ by simpa using hd₂ n
    map := U₂
    asymptoticallyMultiplicative := hU₂ }
  let C : KazhdanCompressionCore Γ H := {
    iota := iota
    t := s
    c := 1
    kazhdan := hasKazhdanPropertyT_iff_textbook.mpr hT
    compresses := hs
    comm_c := fun γ ↦ Commute.one_left (iota γ) }
  have hcard : ∀ n : ℕ,
      ((Fintype.card (naturalFiniteModel (d₁ n)) : ℝ) +
        Fintype.card (naturalFiniteModel (d₂ n))) =
        (d₁ n : ℝ) + d₂ n := by
    intro n
    simp
  have hpos : ∀ n : ℕ, (0 : ℝ) < (d₁ n : ℝ) + d₂ n := by
    intro n
    have h : 0 < d₁ n + d₂ n := Nat.add_pos_left (hd₁ n) _
    exact_mod_cast h
  have hxI : IsAsymptoticIntertwiner B₁ B₂ C x := by
    intro γ ε hε
    obtain ⟨N, hN⟩ := hx γ (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hsq := hN n hn
    have hmass : 0 ≤ rectMass (x n -
        (U₁ n (iota γ) : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) * x n *
        (U₂ n (iota γ) : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ)ᴴ) := rectMass_nonneg _
    have hdiv : rectMass (x n -
        (U₁ n (iota γ) : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) * x n *
        (U₂ n (iota γ) : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ)ᴴ) / ((d₁ n : ℝ) + d₂ n) ≤ ε := by
      calc
        rectMass (x n -
            (U₁ n (iota γ) : Matrix (naturalFiniteModel (d₁ n))
              (naturalFiniteModel (d₁ n)) ℂ) * x n *
            (U₂ n (iota γ) : Matrix (naturalFiniteModel (d₂ n))
              (naturalFiniteModel (d₂ n)) ℂ)ᴴ) / ((d₁ n : ℝ) + d₂ n) =
            (Real.sqrt (rectMass (x n -
              (U₁ n (iota γ) : Matrix (naturalFiniteModel (d₁ n))
                (naturalFiniteModel (d₁ n)) ℂ) * x n *
              (U₂ n (iota γ) : Matrix (naturalFiniteModel (d₂ n))
                (naturalFiniteModel (d₂ n)) ℂ)ᴴ) /
              ((d₁ n : ℝ) + d₂ n))) ^ 2 :=
          (Real.sq_sqrt (div_nonneg hmass (hpos n).le)).symm
        _ ≤ (Real.sqrt ε) ^ 2 :=
          (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hsq
        _ = ε := Real.sq_sqrt hε.le
    have hgoal := (div_le_iff₀ (hpos n)).mp hdiv
    rw [← hcard n] at hgoal
    exact hgoal
  have hxB : IsUniformlyBoundedRect B₁ B₂ x := hbound
  have htrans := it_05_intertwiner_transport hUP B₁ B₂ C x hxI hxB
  intro γ ε hε
  obtain ⟨N, hN⟩ := htrans γ (ε ^ 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hval := hN n hn
  rw [hcard n] at hval
  have hdiv : rectMass ((fun n ↦
      (U₁ n s : Matrix (naturalFiniteModel (d₁ n))
        (naturalFiniteModel (d₁ n)) ℂ) * x n *
      (U₂ n s : Matrix (naturalFiniteModel (d₂ n))
        (naturalFiniteModel (d₂ n)) ℂ)ᴴ) n -
      (U₁ n (iota γ) : Matrix (naturalFiniteModel (d₁ n))
        (naturalFiniteModel (d₁ n)) ℂ) *
        ((fun n ↦ (U₁ n s : Matrix (naturalFiniteModel (d₁ n))
          (naturalFiniteModel (d₁ n)) ℂ) * x n *
          (U₂ n s : Matrix (naturalFiniteModel (d₂ n))
            (naturalFiniteModel (d₂ n)) ℂ)ᴴ) n) *
        (U₂ n (iota γ) : Matrix (naturalFiniteModel (d₂ n))
          (naturalFiniteModel (d₂ n)) ℂ)ᴴ) /
      ((d₁ n : ℝ) + d₂ n) ≤ ε ^ 2 :=
    (div_le_iff₀ (hpos n)).mpr hval
  have hsqrt := Real.sqrt_le_sqrt hdiv
  rw [Real.sqrt_sq hε.le] at hsqrt
  exact hsqrt

/-- **`thm:transport-variants`(2) at every weight, by the ultraproduct
route — NOT CLOSED.  Do not badge this declaration.**

"The same reduction through (1) gives the intertwiner transport at every
weight": the block reduction is weight-blind, so feeding it the weighted
transport `_hUPs` (part (1)) transports every `w`-mass-bounded, `w`-scaled
asymptotic intertwiner.  `_hUPs` is an unproved hypothesis; see the STATUS
block at the head of this file.  The statement is otherwise identical to
`IntertwinerKazhdanTransport.scaled_intertwiner_transport`, which *is*
closed, by the finite-stage route. -/
theorem scaled_ultraproduct_intertwiner_transport :
    ∀ {Γ E : Type} [Group Γ] [Group E]
      (_hUPs : UltraproductScaledTransportFor Γ E)
      (B₁ B₂ : OpAlmostRepresentation E)
      (w : ℕ → ℝ) (_hw : ∀ n, 0 ≤ w n) (C : KazhdanCompressionCore Γ E)
      (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ)
      (_hx : IsScaledAsymptoticIntertwinerOf B₁ B₂ w C.iota x)
      (_hbound : IsScaledRectMassBounded B₁ B₂ w x),
      IsScaledAsymptoticIntertwinerOf B₁ B₂ w C.iota (fun n ↦
        (B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
          (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) := by
  intro Γ E _ _ hUPs B₁ B₂ w hw C x hx hbound
  exact it_06_scaled_intertwiner_transport hUPs B₁ B₂ w hw C x hx hbound

end UltraproductIntertwinerTransport
end GroupApproximation
