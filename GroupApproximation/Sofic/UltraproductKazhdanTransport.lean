import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann
import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Analysis.ProperIsometryFromCompression
import GroupApproximation.Sofic.LeavittTraceFloor
import GroupApproximation.Sofic.UltraproductDedekindFinite
import GroupApproximation.Sofic.PrintedTransportOpening
import GroupApproximation.Sofic.UltraproductKazhdanProjection
import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# The printed ultraproduct proof of Kazhdan transport: steps KT.10 and KT.11

This file certifies the last two steps of the **printed** proof of
`\ref{thm:kazhdan-transport}` in `non_mf_groups_exist.tex`, together with
the by-contradiction skeleton that the printed proof runs.  A second,
quantitative finite-stage proof is formalized in
`Sofic/ManuscriptKazhdanTransport.lean`; the manuscript printed it as an
appendix until commit `3a45fa60` cut it, and what is replayed here is the
ultraproduct proof, which is the one still in print.

Anchors in the TeX, in decreasing stability: the label
`thm:kazhdan-transport`; the enclosing
`\section{One-sided conjugation in matrix models}` (`\ref{sec:transport}`); and
the five italicized paragraph headings of the printed proof, which are the
step boundaries used below --
`\emph{The adjoint model.}`, `\emph{The ultraproduct.}`,
`\emph{The projection onto the fixed subspace.}`,
`\emph{The two projections agree.}`, `\emph{Conclusion.}`.
Line numbers are deliberately not cited: the manuscript is under concurrent
edit and every offset in this repository's notes is stale within minutes.
Re-grep the labels and the headings rather than trusting any offset.

The manuscript's proof ledger is

```
KT.01  the adjoint model  K_n = L²(M_{d n}, tr_{d n}),  Ad U_n(g) ξ = U_n(g) ξ U_n(g)*
KT.02  the Hilbert-space ultraproduct  K_ω
KT.03  the norm ultraproduct  B_ω = ∏_ω B(K_n)  acting on  K_ω
KT.04  faithfulness of that action, hence  ran P ⊆ ran Q → P ≤ Q
KT.05  π : H → U(B_ω),  π g = [Ad U_n g]_ω,  is a homomorphism
KT.06  B_ω is finite:  σ*σ = 1 → σσ* = 1
KT.07  the Kazhdan spectral gap for the averaged operator h
KT.08  the Kazhdan projection P, with  ran P = Fix
KT.09  V = π s,  Q = V P V*,  and  Fix ⊆ V·Fix,  i.e.  P ≤ Q
KT.10  r = V*Q,  σ = r + (1 - Q)  is an isometry; finiteness makes σ unitary,
       and  σσ* = P + (1 - Q)  forces  Q = P
KT.11  ξ = [ξ_n]_ω  is fixed by every π(ι γ); Q = P puts V ξ in Fix, which is
       the asserted Hilbert--Schmidt vanishing along ω, contradicting I ∈ ω
```

Steps KT.01--KT.09 build the ambient; they are supplied here as the bundled
interface `UltraproductAdjointModel`, one field per manuscript sentence.
Steps **KT.10** (`kt_10_finiteness_reverses_conjugate`, together with the
isometry identities `kt_10_isometry_identities`) and **KT.11**
(`UltraproductAdjointModel.kt_11_descend`) are proved in full, and
`ultraproductKazhdanTransport` runs the manuscript's contradiction:
the conclusion fails on an infinite set `I`, a free ultrafilter `ω` with
`I ∈ ω` is fixed, KT.11 makes the commutators vanish along `ω`, and `I ∈ ω`
is contradicted.

That sentence was aspirational until 2026-08-18 and is now literal, which is
worth being precise about because ledger row `KT.01` turned on the difference.
The proof used to reach the conclusion *directly*: it proved vanishing along
every free ultrafilter and handed that to `tendsto_along_free_ultrafilters`,
which is where the contradiction happened -- for an arbitrary nonnegative
sequence, with `ω` produced from a cofinal selection rather than chosen to
contain the printed `I`.  The opening is now taken at the printed objects,
through `PrintedTransportOpening.exists_gamma_infinite_commutator_defect` and
`UltrafilterLimit.exists_freeUltrafilter_mem`, so the route and the printed
proof are the same argument and not merely the same theorem.

**Status, stated plainly.**  `UltraproductAdjointModel` now has a constructor:
`Sofic/UltraproductModelConstructionAssembly.lean` builds one at every free
ultrafilter from the hypotheses of `thm:kazhdan-transport` itself, assembling
the vector ultraproduct and the action of
`Sofic/UltraproductModelConstruction.lean`, the finiteness of
`Sofic/UltraproductDedekindFinite.lean`, and the Kazhdan projection of
`Sofic/UltraproductKazhdanProjection.lean`.  Everything below that consumes the
interface -- `kt_11_descend` and `ultraproductKazhdanTransport` -- is therefore
a statement about an ambient that exists, and
`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport` is derived through this
chain.  Unconditional here with no interface at all, as before: all the
Hilbert--Schmidt lemmas, both KT.10 theorems on the real objects
(`kt_10_shift_conjugate_proj`, `kt_10_corona_shift_conjugate_proj`), and the
ultrafilter skeleton `tendsto_along_free_ultrafilters` -- which the transport
proof no longer travels, and which ledger row `KT.28` cites for a step of its
own.

**What is still *not* the printed argument.**  This is the canonical record;
`notes/NON_MF_PROOF_LEDGER.md` tracks the same three items as UF.01, UF.02 and
UF.03.  Each is a deviation, not a closure, and none of them is repaired by
anything in this file.

* **UF.01, UF.03 -- no ultraproduct along a genuine free `ω`.**  The algebra
  realizing `B_ω` is the *cofinite* norm corona `∏_∞ B(K_n)`, not the printed
  `∏_ω B(K_n)`.  Because `ω ≤ cofinite` the cofinite-null ideal sits inside the
  `ω`-null ideal, so `∏_∞ B(K_n) ↠ ∏_ω B(K_n)`; `π` and `P` are lifts of the
  manuscript's objects and the identity `Q = P` proved upstairs descends.  That
  is why the substitution costs the *transport theorem* nothing.  It is not a
  construction of `∏_ω B(K_n)`.  Note that `\label{lem:ultrafinite}` no longer
  asserts anything about `∏_ω`: as printed it is finiteness of the `c₀`-quotient
  `B_c = ∏_n B(K_n)/⊕_n B(K_n)`, which is exactly
  `Sofic/UltraproductDedekindFinite.kt_06_ultraproduct_finite`.  The passage to
  a free ultrafilter now lives in *unnumbered prose* after that lemma, is used
  by the printed proof below, and is invisible to any gate that reads only
  numbered environments.
* **UF.02 -- faithfulness of the action on `K_ω` is neither proved nor used.**
  It is *false* for the corona surrogate: see the docstring of
  `Sofic/UltraproductDedekindFinite.kt_06_ultraproduct_finite` for the explicit
  counterexample.  The chain survives because it never needs it -- `Fix ⊆ V·Fix`
  is read back as `P ≤ Q` through the algebraic absorption identities
  `UltraproductKazhdanProjection.kt_09_*` rather than through an inclusion of
  ranges.  A hypothesis the printed proof requires and the formal proof does not
  is a genuine divergence and is recorded as one.
* **`K_ω` carries no inner product.**  `UltraproductModelConstruction.Vec` is
  the underlying complex vector space of the Hilbert-space ultraproduct --
  mass-bounded families modulo `ω`-null families -- and nothing below asks for
  more, which is precisely why the printed route could be formalized without
  the Hilbert structure.  No declaration in this development calls `Vec` a
  Hilbert space.

`\label{lem:finitecompare}`, the third item the earlier audit recorded as a
mismatch, *is* closed: `kt_10_finiteness_reverses` below is now the printed
generic comparison lemma, not the unitary-conjugation special case.

KT.10 additionally lands on the real objects, with nothing assumed:
`kt_10_shift_conjugate_proj` closes it for the KT.07--KT.09 bundle
`UltraproductKazhdanProjection.KazhdanCompressionRep`, and
`kt_10_corona_shift_conjugate_proj` specializes that to
`B_ω = NormMatrixCStarCorona X`, where finiteness is the instance
`normMatrixCStarCorona_isDedekindFiniteMonoid` rather than a hypothesis.

`kt_10_finiteness_reverses` is the *generic* comparison lemma the manuscript
factors out as `\label{lem:finitecompare}` -- finite unital C-star algebra,
projections `p ≤ q` with `p ∼ q` in the Murray--von Neumann sense, conclusion
`p = q` -- and it is proved by the printed `σ = r + (1 - q)` calculation in
`Analysis/FiniteCStarMurrayVonNeumann.lean`.  It is deliberately *not* stated
with `q = V p V*`: unitary conjugacy is strictly stronger than Murray--von
Neumann equivalence, so that form would certify less than the printed sentence.

KT.10 is *not* reproved here: `Analysis/ProperIsometryFromCompression.lean`
already contains the whole calculation, with `r = V*Q = P V*` the first
summand of `ProperProjectionCompression.isometry`,
`star_isometry_mul_isometry` the identity `σ*σ = Q + (1 - Q) = 1`,
`isometry_mul_star_isometry` the identity `σσ* = 1 - (Q - P) = P + (1 - Q)`,
and `unitary_conjugate_eq_of_absorbs` the passage from Dedekind finiteness to
`Q = P`.  This file only applies it.

The trap recorded in `notes/NOTEPAD.md` under the heading
"The Hilbert-ultraproduct trap in defect-localized commutant pinning" is
avoided exactly as the
manuscript avoids it: the hypotheses kept live are the **operator-norm**
uniform bound on `(x_n)` and the **operator-norm** almost multiplicativity of
`U_n`, never a bare Hilbert--Schmidt bound.  The operator-norm bound enters
through `hsNormSq_le_mul_self_l2_opNorm`, which is what makes the class
`ξ = [ξ_n]_ω` well defined.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

/-! ## Normalized Hilbert--Schmidt facts used by the descent -/

/-- The identity matrix has normalized Hilbert--Schmidt norm one. -/
theorem hsNormSq_one (Y : FiniteModel) (hY : 0 < Fintype.card Y) :
    hsNormSq Y (1 : Matrix Y Y ℂ) = 1 := by
  have hcard : ((Fintype.card Y : ℕ) : ℝ) ≠ 0 :=
    (Nat.cast_ne_zero (R := ℝ)).mpr hY.ne'
  have hrow : ∀ i : Y,
      (∑ j : Y, Complex.normSq ((1 : Matrix Y Y ℂ) i j)) = 1 := by
    intro i
    have hstep : ∀ j : Y, Complex.normSq ((1 : Matrix Y Y ℂ) i j)
        = if j = i then (1 : ℝ) else 0 := by
      intro j
      by_cases h : j = i
      · subst h
        rw [Matrix.one_apply_eq]
        simp
      · rw [Matrix.one_apply_ne (Ne.symm h)]
        simp [h]
    rw [Finset.sum_congr rfl fun j _ ↦ hstep j]
    simp
  have hdouble : (∑ i : Y, ∑ j : Y, Complex.normSq ((1 : Matrix Y Y ℂ) i j))
      = (Fintype.card Y : ℝ) := by
    calc (∑ i : Y, ∑ j : Y, Complex.normSq ((1 : Matrix Y Y ℂ) i j))
        = ∑ _i : Y, (1 : ℝ) := Finset.sum_congr rfl fun i _ ↦ hrow i
      _ = (Fintype.card Y : ℝ) := by simp [Finset.card_univ]
  rw [hsNormSq, hdouble, div_self hcard]

/-- Negation does not move the normalized Hilbert--Schmidt norm. -/
theorem hsNormSq_neg (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    hsNormSq Y (-A) = hsNormSq Y A := by
  have hentry : ∀ i j : Y,
      Complex.normSq ((-A) i j) = Complex.normSq (A i j) := by
    intro i j
    rw [Matrix.neg_apply, Complex.normSq_neg]
  have hsum : (∑ i : Y, ∑ j : Y, Complex.normSq ((-A) i j))
      = ∑ i : Y, ∑ j : Y, Complex.normSq (A i j) :=
    Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ hentry i j
  rw [hsNormSq, hsNormSq, hsum]

/-- Conjugate transposition preserves the unitary group. -/
theorem unitaryGroup_conjTranspose_mem {Y : FiniteModel} {W : Matrix Y Y ℂ}
    (hW : W ∈ Matrix.unitaryGroup Y ℂ) : Wᴴ ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact Unitary.star_mul_self_of_mem hW

/-- **The operator norm dominates the normalized Hilbert--Schmidt norm.**
This is the estimate behind the manuscript's remark that "the uniform
operator-norm bound makes `ξ` well defined": it is the only place where the
operator-norm hypothesis on `(x_n)` is consumed, and it is exactly what the
invalid variant of the argument recorded in `notes/NOTEPAD.md` lacks. -/
theorem hsNormSq_le_mul_self_l2_opNorm (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (A : Matrix Y Y ℂ) :
    hsNormSq Y A ≤ ‖A‖ * ‖A‖ := by
  have h := hsNormSq_mul_le_sq_l2_opNorm_mul Y A 1
  rw [Matrix.mul_one, hsNormSq_one Y hY, mul_one] at h
  calc hsNormSq Y A ≤ ‖A‖ ^ 2 := h
    _ = ‖A‖ * ‖A‖ := by ring

/-- The adjoint action `Ad W` is an isometry of the normalized
Hilbert--Schmidt norm. -/
theorem hsNormSq_conjugate (Y : FiniteModel) {W : Matrix Y Y ℂ}
    (hW : W ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y)
    (A : Matrix Y Y ℂ) : hsNormSq Y (W * A * Wᴴ) = hsNormSq Y A := by
  rw [hsNormSq_mul_right Y (unitaryGroup_conjTranspose_mem hW),
    hsNormSq_mul_left Y hW hY]

/-- **Unitary invariance in the manuscript's form.**  The adjoint displacement
`Ad W (A) - A` has exactly the normalized Hilbert--Schmidt length of the
commutator `A W - W A`.  This is the sentence "by unitary invariance of the
normalized Hilbert--Schmidt norm, the commutator hypothesis says exactly that
each `π(ι γ)` fixes `ξ`", and it is used again in the other direction at the
end of the printed proof. -/
theorem hsNormSq_adjoint_sub (Y : FiniteModel) {W : Matrix Y Y ℂ}
    (hW : W ∈ Matrix.unitaryGroup Y ℂ) (A : Matrix Y Y ℂ) :
    hsNormSq Y (W * A * Wᴴ - A) = hsNormSq Y (A * W - W * A) := by
  have hWW : W * Wᴴ = 1 := Unitary.mul_star_self_of_mem hW
  have hexp : (A * W - W * A) * Wᴴ = A * (W * Wᴴ) - W * A * Wᴴ := by
    noncomm_ring
  have hfactor : W * A * Wᴴ - A = -((A * W - W * A) * Wᴴ) := by
    rw [hexp, hWW, Matrix.mul_one]
    abel
  rw [hfactor, hsNormSq_neg,
    hsNormSq_mul_right Y (unitaryGroup_conjTranspose_mem hW)]

/-! ## KT.10: finiteness reverses the one-sided compression

The manuscript writes `r = V*Q`, `σ = r + (1 - Q)`, and computes
`σ*σ = Q + (1 - Q) = 1` and `σσ* = P + (1 - Q)`.  Since `V` is unitary,
`r = V*(V P V*) = P V*`, so `σ` is literally
`ProperProjectionCompression.isometry`, and the two computations are the two
theorems of `Analysis/ProperIsometryFromCompression.lean`. -/

/-- The manuscript's element `r = V*Q` is the first summand `P V*` of
`ProperProjectionCompression.isometry`. -/
theorem kt_10_star_unitary_mul_conjugate
    {A : Type u} [Ring A] [StarRing A] (D : ProperProjectionCompression A) :
    star D.u * D.q = D.p * star D.u := by
  have hq : D.q = D.u * D.p * star D.u := rfl
  rw [hq]
  calc star D.u * (D.u * D.p * star D.u)
      = (star D.u * D.u) * (D.p * star D.u) := by noncomm_ring
    _ = D.p * star D.u := by rw [D.u_star_mul, one_mul]

/-- **KT.10, the two computations.**  With `r = V*Q` and `σ = r + (1 - Q)`,
the manuscript's identities `σ*σ = 1` and `σσ* = P + (1 - Q)` hold verbatim. -/
theorem kt_10_isometry_identities
    {A : Type u} [Ring A] [StarRing A] (D : ProperProjectionCompression A) :
    D.isometry = star D.u * D.q + (1 - D.q) ∧
      star D.isometry * D.isometry = 1 ∧
      D.isometry * star D.isometry = D.p + (1 - D.q) := by
  refine ⟨?_, D.star_isometry_mul_isometry, ?_⟩
  · rw [kt_10_star_unitary_mul_conjugate D]
    rfl
  · rw [D.isometry_mul_star_isometry]
    abel

/-- **`\label{lem:finitecompare}`, the manuscript's comparison lemma.**  Let `A`
be a finite unital C-star algebra and let `p, q ∈ A` be projections with
`p ≤ q` and `p ∼ q`.  Then `p = q`.

Both printed conventions are taken literally, from the display of the three
"manifestations of one finiteness principle" just above the lemma: `p ∼ q` is
Murray--von Neumann equivalence, `MurrayVonNeumannEquiv`, so the implementer is
an arbitrary partial isometry and not a unitary conjugation; and *finite* is
"every isometry in it is unitary", the hypothesis `hfinite`, rather than the
formally stronger `IsDedekindFiniteMonoid`.  `p ≤ q` is the genuine C-star
order, whose two side instances `PartialOrder` and `StarOrderedRing` are the
standard Mathlib inputs needed to write `≤` at all, installed for a concrete
algebra by `CStarAlgebra.spectralOrder` and `CStarAlgebra.spectralOrderedRing`.

The proof is the printed one --- `r = rq`, `r = pr`, `r = qr`, the vanishing
cross terms, `σ = r + (1 - q)` with `σ*σ = 1`, and finiteness turning
`σσ* = p + (1 - q)` into `1` --- executed in
`Analysis/FiniteCStarMurrayVonNeumann.lean`.

The earlier, strictly weaker form of this declaration fixed `q = V p V*` for a
*unitary* `V`.  That special case is not lost: it is
`ProperProjectionCompression.unitary_conjugate_eq_of_absorbs`, which the two
theorems below now call directly, and which is genuinely incomparable with the
statement here --- it holds in a bare star ring, where the printed derivation of
`r = rq` and `r = pr` is unavailable, while this one needs only one of the two
isometry identities. -/
theorem kt_10_finiteness_reverses :
    ∀ {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      (_hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
      {p q : A} (_hp : IsStarProjection p) (_hq : IsStarProjection q)
      (_hle : p ≤ q) (_hmvn : MurrayVonNeumannEquiv p q),
      p = q := by
  intro A _ _ _ hfinite p q hp hq hle hmvn
  exact finiteCStar_eq_of_le_of_murrayVonNeumannEquiv hfinite hp hq hle hmvn

/-- **KT.10 through the Murray--von Neumann step.**  The instance of
`kt_10_finiteness_reverses` that the transport proof consumes: in a
Dedekind-finite unital C-star algebra a projection absorbed by an isometry
conjugate of itself equals that conjugate.

This is the manuscript's sentence "the inclusion `s ι(Γ) s⁻¹ ⊆ ι(Γ)` implies
`P ≤ V P V*`, the two projections are Murray--von Neumann equivalent, and the
ultraproduct is finite, so `P = V P V*`", and it travels that route: the
equivalence is `MurrayVonNeumannEquiv.of_isometry_conjugate` and the comparison
is the lemma above.  Dedekind finiteness is what discharges the manuscript's
`hfinite`, since it is the class the repository's only finiteness witness
`normMatrixCStarCorona_isDedekindFiniteMonoid` lives in. -/
theorem kt_10_finiteness_reverses_conjugate {A : Type u} [CStarAlgebra A]
    [IsDedekindFiniteMonoid A] {p u : A}
    (hp_star : star p = p) (hp_idem : p * p = p)
    (hu_star_mul : star u * u = 1)
    (hqp : (u * p * star u) * p = p) :
    u * p * star u = p :=
  dedekindFiniteCStar_isometry_conjugate_eq_of_absorbs
    ⟨hp_idem, hp_star⟩ hu_star_mul hqp

/-! ### KT.10 on the manuscript's own objects

`Sofic/UltraproductKazhdanProjection.lean` delivers steps KT.07--KT.09 as the
bundle `KazhdanCompressionRep Γ H B` in an abstract unital C-star algebra `B`,
and `Sofic/UltraproductDedekindFinite.lean` delivers KT.06 as the instance
`normMatrixCStarCorona_isDedekindFiniteMonoid`.  The two theorems below close
KT.10 on exactly those objects: no hypothesis stands in for KT.06, KT.08 or
KT.09, and the finiteness of `B_ω` is an instance, not an assumption. -/

section CompressionBundle

open UltraproductKazhdanProjection

/-- **KT.10 on the Kazhdan compression bundle.**  In a Dedekind-finite unital
C-star algebra, the conjugated Kazhdan projection `Q = V P V*` equals `P`.

The inputs are exactly the manuscript's: `P` is a projection
(`kt_08_isSelfAdjoint_proj`, `kt_08_proj_mul_proj`), `V = π(s)` is an isometry
(`shift_star_mul`), and `P ≤ Q` (`kt_09_conjugate_mul_proj`).  Finiteness does
the rest, through the Murray--von Neumann step of
`kt_10_finiteness_reverses`.  The second unitary identity `shift_mul_star` and
the mirrored absorption `kt_09_proj_mul_conjugate` are not consumed: the first
because the comparison lemma needs only one isometry identity, the second
because it is the star of the first. -/
theorem kt_10_shift_conjugate_proj
    {Γ : Type*} {H : Type*} {B : Type*}
    [Group Γ] [Group H] [CStarAlgebra B] [IsDedekindFiniteMonoid B]
    (D : KazhdanCompressionRep Γ H B) :
    D.shift * D.proj * star D.shift = D.proj :=
  kt_10_finiteness_reverses_conjugate
    D.kt_08_isSelfAdjoint_proj.star_eq
    D.kt_08_proj_mul_proj
    D.shift_star_mul
    D.kt_09_conjugate_mul_proj

/-- **KT.10 in the norm ultraproduct `B_ω` itself.**  Specializing the
previous theorem to `B_ω = NormMatrixCStarCorona X` discharges the finiteness
hypothesis outright: `normMatrixCStarCorona_isDedekindFiniteMonoid` is an
instance, so this statement carries no `Prop` premise beyond the compression
bundle.  This is the manuscript's sentence "Finiteness of `B_ω` makes `σ`
unitary, and `σσ* = P + (1 - Q)` forces `Q = P`", on the real algebra. -/
theorem kt_10_corona_shift_conjugate_proj
    {Γ : Type*} {H : Type*} [Group Γ] [Group H]
    (X : ℕ → Type u) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)]
    (D : KazhdanCompressionRep Γ H (NormMatrixCStarCorona X)) :
    D.shift * D.proj * star D.shift = D.proj :=
  kt_10_shift_conjugate_proj D

end CompressionBundle

/-! ## The ultrafilter skeleton of the printed proof -/

/-- The manuscript's `→ 0` written as a filter limit. -/
theorem tendsto_of_sqrt_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, Real.sqrt (f n) ≤ ε) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  obtain ⟨N, hN⟩ := h (Real.sqrt (δ / 2)) (Real.sqrt_pos.mpr hhalf)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h1 : Real.sqrt (f n) * Real.sqrt (f n)
      ≤ Real.sqrt (δ / 2) * Real.sqrt (δ / 2) :=
    mul_self_le_mul_self (Real.sqrt_nonneg _) (hN n hn)
  rw [Real.mul_self_sqrt (hf n), Real.mul_self_sqrt hhalf.le] at h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf n)]
  linarith

/-- **The manuscript's contradiction skeleton.**  Suppose the conclusion
fails: there are `δ > 0` and an infinite set `I ⊆ ℕ` with `√(f n) ≥ δ` for
`n ∈ I`.  A free ultrafilter `ω` with `I ∈ ω` is produced from a selector
enumerating `I` cofinally, and vanishing of `f` along every free ultrafilter
contradicts `I ∈ ω`.  Since the failing subsequence was arbitrary, the full
sequence converges. -/
theorem tendsto_along_free_ultrafilters {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
      Filter.Tendsto f (ω : Filter ℕ) (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, Real.sqrt (f n) ≤ ε := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  -- `hcon` is the manuscript's infinite bad set `I`, presented cofinally.
  choose sel hselge hselbad using hcon
  have hid : Filter.Tendsto (fun n : ℕ ↦ n) Filter.atTop Filter.atTop :=
    Filter.tendsto_id
  have hseltop : Filter.Tendsto sel Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ (hselge n : n ≤ sel n)) hid
  haveI : (Filter.map sel Filter.atTop).NeBot := inferInstance
  -- a free ultrafilter containing the bad set
  let ω : Ultrafilter ℕ := Ultrafilter.of (Filter.map sel Filter.atTop)
  have hωle : (ω : Filter ℕ) ≤ Filter.map sel Filter.atTop :=
    Ultrafilter.of_le (Filter.map sel Filter.atTop)
  have hωcof : (ω : Filter ℕ) ≤ Filter.cofinite := by
    refine le_trans hωle ?_
    rw [Nat.cofinite_eq_atTop]
    exact hseltop
  have hbad : {n : ℕ | ε < Real.sqrt (f n)} ∈ (ω : Filter ℕ) := by
    have hmem : {n : ℕ | ε < Real.sqrt (f n)} ∈ Filter.map sel Filter.atTop := by
      rw [Filter.mem_map]
      have huniv : sel ⁻¹' {n : ℕ | ε < Real.sqrt (f n)} = Set.univ := by
        ext k
        simp [hselbad k]
      rw [huniv]
      exact Filter.univ_mem
    exact hωle hmem
  have hconv := h ω hωcof
  have hsmall : ∀ᶠ n in (ω : Filter ℕ), f n < ε * ε :=
    ((Metric.tendsto_nhds.mp hconv) (ε * ε) (mul_pos hε hε)).mono fun n hn ↦ by
      have h1 : |f n - 0| < ε * ε := by
        rw [← Real.dist_eq]
        exact hn
      rwa [sub_zero, abs_of_nonneg (hf n)] at h1
  have hbadev : ∀ᶠ n in (ω : Filter ℕ), ε < Real.sqrt (f n) :=
    Filter.eventually_iff.mpr hbad
  obtain ⟨n, hn1, hn2⟩ := (hbadev.and hsmall).exists
  have hsq : ε * ε < Real.sqrt (f n) * Real.sqrt (f n) :=
    mul_self_lt_mul_self hε.le hn1
  rw [Real.mul_self_sqrt (hf n)] at hsq
  linarith

/-! ## The KT.01--KT.09 interface -/

/-- The matrix algebra `M_{d n}(ℂ)` in the manuscript's natural coordinates. -/
abbrev NatMatrix (d : ℕ → ℕ) (n : ℕ) : Type :=
  Matrix (naturalFiniteModel (d n)) (naturalFiniteModel (d n)) ℂ

/-- The underlying matrix of the model unitary `U_n(g)`. -/
@[reducible] def natU {H : Type*} {d : ℕ → ℕ}
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (n : ℕ) (g : H) : NatMatrix d n :=
  (U n g : Matrix (naturalFiniteModel (d n)) (naturalFiniteModel (d n)) ℂ)

/-- `U_n(g)` is unitary. -/
theorem natU_mem {H : Type*} {d : ℕ → ℕ}
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (n : ℕ) (g : H) :
    natU U n g ∈ Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ :=
  (U n g).2

/-- **The ambient produced by manuscript steps KT.01--KT.09**, bundled.

Each field is one sentence of the printed proof:

* `Alg`, `ring`, `starRing` -- the norm ultraproduct `B_ω = ∏_ω B(K_n)` (KT.03);
* `dedekindFinite` -- "the algebra `B_ω` is *finite*", proved there by polar
  correction of a family `σ_n` with `‖σ_n*σ_n - 1‖ → 0` (KT.06);
* `Vec`, `act`, `act_mul` -- the Hilbert-space ultraproduct `K_ω` and the
  action `[A_n]_ω[ξ_n]_ω = [A_n ξ_n]_ω` (KT.02, KT.03);
* `cls`, `cls_eq_iff` -- the class `[ξ_n]_ω` of a uniformly bounded family of
  matrices, each regarded as a vector of `K_n = L²(M_{d n}, tr_{d n})`, and
  the fact that two such classes agree exactly when the difference is null
  along `ω` (KT.02, and KT.04 in the direction that reads an equality of
  vectors back off the sequences);
* `pi`, `pi_star`, `act_pi_cls` -- the homomorphism `π g = [Ad U_n g]_ω` into
  the unitaries of `B_ω` and its action on classes (KT.01, KT.05);
* `P`, `P_star`, `P_mul_P`, `rep_mul_P`, `act_P_cls_of_fixed` -- the Kazhdan
  projection at the isolated spectral point `1` and the identification
  `ran P = Fix` (KT.07, KT.08).  The two inclusions are deliberately not
  bundled as one `iff`: `ran P ⊆ Fix` is the purely algebraic `rep_mul_P`,
  which `UltraproductKazhdanProjection.kt_08_rep_mul_proj` already proves, and
  the vector-level direction is *derived* from it in
  `act_pi_iota_of_act_P`.  Only `Fix ⊆ ran P` is assumed, and only for
  classes of uniformly bounded families;
* `P_mul_conjugate`, `conjugate_mul_P` -- `Fix ⊆ V·Fix` read back as
  `P ≤ Q` for `Q = V P V*`, `V = π s` (KT.04, KT.09).

Every field is an intermediate object of the manuscript's own proof; none is a
hypothesis about the *theorem*, and each is discharged by
`UltraproductModelConstruction.ultraproductAdjointModel` from the hypotheses of
`thm:kazhdan-transport` alone. -/
structure UltraproductAdjointModel
    {Γ : Type} {H : Type*} [Group Γ] [Group H]
    (iota : Γ →* H) (s : H) (d : ℕ → ℕ)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (ω : Ultrafilter ℕ) where
  /-- KT.03: the carrier of the norm ultraproduct `B_ω = ∏_ω B(K_n)`. -/
  Alg : Type
  /-- `B_ω` is a ring. -/
  [ring : Ring Alg]
  /-- `B_ω` is a star ring. -/
  [starRing : StarRing Alg]
  /-- KT.06: `B_ω` is finite, i.e. `σ*σ = 1` forces `σσ* = 1`.  When `Alg` is
  instantiated at the real ambient `NormMatrixCStarCorona X` this field is
  `inferInstance`: `Sofic/UltraproductDedekindFinite.lean` registers
  `normMatrixCStarCorona_isDedekindFiniteMonoid`, and proves it as printed via
  `kt_06_polar_correction` and `kt_06_ultraproduct_finite`. -/
  [dedekindFinite : IsDedekindFiniteMonoid Alg]
  /-- KT.02: the carrier of the Hilbert-space ultraproduct `K_ω`. -/
  Vec : Type
  /-- KT.03: the action of `B_ω` on `K_ω`. -/
  act : Alg → Vec → Vec
  /-- The action is an action of the multiplicative structure. -/
  act_mul : ∀ (a b : Alg) (ζ : Vec), act (a * b) ζ = act a (act b ζ)
  /-- KT.02: the class `[ξ_n]_ω ∈ K_ω` of a family of matrices, each read as a
  vector of `K_n = L²(M_{d n}, tr_{d n})`. -/
  cls : (∀ n, NatMatrix d n) → Vec
  /-- KT.02 and KT.04: two uniformly bounded families have the same class in
  `K_ω` exactly when their difference is Hilbert--Schmidt null along `ω`. -/
  cls_eq_iff : ∀ (C : ℝ) (ξ η : ∀ n, NatMatrix d n),
      (∀ n, hsNormSq (naturalFiniteModel (d n)) (ξ n) ≤ C) →
      (∀ n, hsNormSq (naturalFiniteModel (d n)) (η n) ≤ C) →
      (cls ξ = cls η ↔
        Filter.Tendsto
          (fun n ↦ hsNormSq (naturalFiniteModel (d n)) (ξ n - η n))
          (ω : Filter ℕ) (nhds 0))
  /-- KT.05: `π : H → U(B_ω)`, `π g = [Ad U_n g]_ω`, is a homomorphism. -/
  pi : H →* Alg
  /-- KT.05: `π` is a star homomorphism, so every `π g` is a unitary. -/
  pi_star : ∀ g : H, star (pi g) = pi g⁻¹
  /-- KT.01 and KT.03: `π g` acts on classes of uniformly bounded families by
  the ultraproduct of the adjoint actions `Ad U_n(g) ξ = U_n(g) ξ U_n(g)*`. -/
  act_pi_cls : ∀ (g : H) (C : ℝ) (ξ : ∀ n, NatMatrix d n),
      (∀ n, hsNormSq (naturalFiniteModel (d n)) (ξ n) ≤ C) →
      act (pi g) (cls ξ) =
        cls (fun n ↦ natU U n g * ξ n * (natU U n g)ᴴ)
  /-- KT.08: the Kazhdan projection, the spectral projection of the averaged
  operator `h` at its isolated spectral point `1`. -/
  P : Alg
  /-- The Kazhdan projection is self-adjoint. -/
  P_star : star P = P
  /-- The Kazhdan projection is idempotent. -/
  P_mul_P : P * P = P
  /-- KT.08, `ran P ⊆ Fix`, in the algebraic form that
  `UltraproductKazhdanProjection.kt_08_rep_mul_proj` already proves verbatim.
  The vector-level inclusion is *derived* from this and `act_mul`, in
  `act_pi_iota_of_act_P`, so it is not assumed. -/
  rep_mul_P : ∀ γ : Γ, pi (iota γ) * P = P
  /-- KT.07 and KT.08, `Fix ⊆ ran P`: this is the half of `ran P = Fix` that
  the spectral gap is *for*, and it is the only genuinely analytic field of
  this structure.  It is stated at exactly the strength `kt_11_descend` uses:
  only for the class of a uniformly bounded family, never for a general vector
  of `K_ω`.

  Whoever discharges this proves it as the manuscript does: a vector fixed by
  every `π(ι s')` is fixed by the average `h`, and since
  `sp(h) ⊆ [-1, 1 - κ²/(2|S|)] ∪ {1}` the spectral projection at the isolated
  point `1` acts as the identity on the `1`-eigenspace of `h`.  The second
  half is a continuous-functional-calculus statement about an eigenvector,
  and no other field of this structure needs it. -/
  act_P_cls_of_fixed : ∀ (C : ℝ) (ξ : ∀ n, NatMatrix d n),
      (∀ n, hsNormSq (naturalFiniteModel (d n)) (ξ n) ≤ C) →
      (∀ γ : Γ, act (pi (iota γ)) (cls ξ) = cls ξ) →
      act P (cls ξ) = cls ξ
  /-- KT.09: `Fix ⊆ V·Fix` read as `P ≤ Q`, first absorption identity. -/
  P_mul_conjugate : P * (pi s * P * star (pi s)) = P
  /-- KT.09: `Fix ⊆ V·Fix` read as `P ≤ Q`, second absorption identity. -/
  conjugate_mul_P : (pi s * P * star (pi s)) * P = P

attribute [instance] UltraproductAdjointModel.ring
  UltraproductAdjointModel.starRing UltraproductAdjointModel.dedekindFinite

namespace UltraproductAdjointModel

variable {Γ : Type} {H : Type*} [Group Γ] [Group H]
  {iota : Γ →* H} {s : H} {d : ℕ → ℕ}
  {U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ}
  {ω : Ultrafilter ℕ}
  (D : UltraproductAdjointModel iota s d U ω)

/-- Every `π g` is a unitary of `B_ω`: the left inverse identity. -/
theorem star_pi_mul_pi (g : H) : star (D.pi g) * D.pi g = 1 := by
  rw [D.pi_star, ← map_mul]
  simp

/-- Every `π g` is a unitary of `B_ω`: the right inverse identity. -/
theorem pi_mul_star_pi (g : H) : D.pi g * star (D.pi g) = 1 := by
  rw [D.pi_star, ← map_mul]
  simp

/-- **KT.10 in the ultraproduct.**  With `V = π s` and `Q = V P V*`, the
one-sided containment `P ≤ Q` of KT.09 and finiteness of `B_ω` force
`Q = P`.

This site cannot route through the manuscript's comparison lemma
`kt_10_finiteness_reverses`: the interface exposes `Alg` as a Dedekind-finite
star ring, and the printed derivation of `r = rq` and `r = pr` from
Murray--von Neumann equivalence needs the C-star input `x*x = 0 → x = 0`.  It
therefore uses `ProperProjectionCompression.unitary_conjugate_eq_of_absorbs`,
which runs the same `σ = r + (1 - q)` calculation with the implementer given by
an explicit formula, so that the two range identities are read off rather than
derived.  On the real ambient `NormMatrixCStarCorona X` the two agree; see
`kt_10_shift_conjugate_proj`, which is the same step with the Murray--von
Neumann equivalence named. -/
theorem kt_10_conjugate_eq : D.pi s * D.P * star (D.pi s) = D.P :=
  ProperProjectionCompression.unitary_conjugate_eq_of_absorbs
    D.P_star D.P_mul_P
    (D.star_pi_mul_pi s) (D.pi_mul_star_pi s)
    D.P_mul_conjugate D.conjugate_mul_P

/-- Since `V P V* = P` and `V` is unitary, `V` commutes with `P`.  This is the
form of `Q = P` used in the concluding paragraph: it turns
`ξ ∈ Fix` into `V ξ ∈ Fix`. -/
theorem pi_mul_P : D.pi s * D.P = D.P * D.pi s := by
  calc D.pi s * D.P
      = D.pi s * D.P * (star (D.pi s) * D.pi s) := by
        rw [D.star_pi_mul_pi s, mul_one]
    _ = (D.pi s * D.P * star (D.pi s)) * D.pi s := by noncomm_ring
    _ = D.P * D.pi s := by rw [D.kt_10_conjugate_eq]

/-- **`ran P ⊆ Fix`, derived.**  A vector in the range of the Kazhdan
projection is fixed by every `π(ι γ)`.  This needs no analysis: it is
`π(ι γ) P = P` moved across the action, and it is why the structure assumes
only the reverse inclusion. -/
theorem act_pi_iota_of_act_P {ζ : D.Vec} (hζ : D.act D.P ζ = ζ) (γ : Γ) :
    D.act (D.pi (iota γ)) ζ = ζ := by
  calc D.act (D.pi (iota γ)) ζ
      = D.act (D.pi (iota γ)) (D.act D.P ζ) := by rw [hζ]
    _ = D.act (D.pi (iota γ) * D.P) ζ := (D.act_mul _ _ _).symm
    _ = D.act D.P ζ := by rw [D.rep_mul_P γ]
    _ = ζ := hζ

/-- **The fixed-vector dictionary.**  For a uniformly bounded family `ξ`, the
class `[ξ_n]_ω` is fixed by `π g` exactly when the normalized
Hilbert--Schmidt commutators `ξ_n U_n(g) - U_n(g) ξ_n` vanish along `ω`.

This is the manuscript's use of unitary invariance, in both directions: at the
start of the concluding paragraph to place `ξ` in `Fix`, and at the end to
read the membership `V ξ ∈ Fix` back as the asserted vanishing. -/
theorem act_pi_cls_eq_iff (hd : ∀ n, 0 < d n) (C : ℝ) (ξ : ∀ n, NatMatrix d n)
    (hξ : ∀ n, hsNormSq (naturalFiniteModel (d n)) (ξ n) ≤ C) (g : H) :
    D.act (D.pi g) (D.cls ξ) = D.cls ξ ↔
      Filter.Tendsto
        (fun n ↦ hsNormSq (naturalFiniteModel (d n))
          (ξ n * natU U n g - natU U n g * ξ n))
        (ω : Filter ℕ) (nhds 0) := by
  have hcard : ∀ n, 0 < Fintype.card (naturalFiniteModel (d n)) := fun n ↦ by
    simpa using hd n
  have hconj : ∀ n, hsNormSq (naturalFiniteModel (d n))
      (natU U n g * ξ n * (natU U n g)ᴴ) ≤ C := by
    intro n
    rw [hsNormSq_conjugate _ (natU_mem U n g) (hcard n)]
    exact hξ n
  have hkey := D.cls_eq_iff C
    (fun n ↦ natU U n g * ξ n * (natU U n g)ᴴ) ξ hconj hξ
  have hpt : ∀ n, hsNormSq (naturalFiniteModel (d n))
        (natU U n g * ξ n * (natU U n g)ᴴ - ξ n)
      = hsNormSq (naturalFiniteModel (d n))
        (ξ n * natU U n g - natU U n g * ξ n) :=
    fun n ↦ hsNormSq_adjoint_sub _ (natU_mem U n g) (ξ n)
  constructor
  · intro hfix
    have h1 : D.cls (fun n ↦ natU U n g * ξ n * (natU U n g)ᴴ) = D.cls ξ := by
      rw [← D.act_pi_cls g C ξ hξ]
      exact hfix
    exact Filter.Tendsto.congr hpt (hkey.mp h1)
  · intro htend
    have h1 : D.cls (fun n ↦ natU U n g * ξ n * (natU U n g)ᴴ) = D.cls ξ :=
      hkey.mpr (Filter.Tendsto.congr (fun n ↦ (hpt n).symm) htend)
    rw [D.act_pi_cls g C ξ hξ]
    exact h1

include D

/-- **KT.11, the descent.**  Let `ξ = [ξ_n]_ω` be the class of the uniformly
bounded family `x`.  By unitary invariance the commutator hypothesis says
exactly that every `π(ι γ)` fixes `ξ`, so `ξ ∈ Fix = ran P`.  Since `Q = P`,
`V ξ ∈ V·Fix = ran Q = ran P = Fix`.  The vector of `U_n(s) x_n U_n(s)*` is
`Ad U_n(s) ξ_n`, so, again by unitary invariance, the conjugated commutators
vanish along `ω`. -/
theorem kt_11_descend (hd : ∀ n, 0 < d n) (C : ℝ) (x : ∀ n, NatMatrix d n)
    (hx : ∀ n, hsNormSq (naturalFiniteModel (d n)) (x n) ≤ C)
    (hcomm : ∀ γ : Γ, Filter.Tendsto
      (fun n ↦ hsNormSq (naturalFiniteModel (d n))
        (x n * natU U n (iota γ) - natU U n (iota γ) * x n))
      (ω : Filter ℕ) (nhds 0))
    (γ : Γ) :
    Filter.Tendsto
      (fun n ↦ hsNormSq (naturalFiniteModel (d n))
        ((natU U n s * x n * (natU U n s)ᴴ) * natU U n (iota γ)
          - natU U n (iota γ) * (natU U n s * x n * (natU U n s)ᴴ)))
      (ω : Filter ℕ) (nhds 0) := by
  have hcard : ∀ n, 0 < Fintype.card (naturalFiniteModel (d n)) := fun n ↦ by
    simpa using hd n
  -- the transported family, with the same uniform bound
  have hy : ∀ n, hsNormSq (naturalFiniteModel (d n))
      (natU U n s * x n * (natU U n s)ᴴ) ≤ C := by
    intro n
    rw [hsNormSq_conjugate _ (natU_mem U n s) (hcard n)]
    exact hx n
  -- ξ ∈ Fix, hence ξ ∈ ran P
  have hfix : D.act D.P (D.cls x) = D.cls x :=
    D.act_P_cls_of_fixed C x hx fun γ' ↦
      (D.act_pi_cls_eq_iff hd C x hx (iota γ')).mpr (hcomm γ')
  -- V ξ ∈ Fix, because Q = P makes V commute with P
  have hVfix : D.act D.P (D.act (D.pi s) (D.cls x))
      = D.act (D.pi s) (D.cls x) := by
    rw [← D.act_mul, ← D.pi_mul_P, D.act_mul, hfix]
  have hall := fun γ' ↦ D.act_pi_iota_of_act_P hVfix γ'
  have hclsy : D.act (D.pi s) (D.cls x)
      = D.cls (fun n ↦ natU U n s * x n * (natU U n s)ᴴ) :=
    D.act_pi_cls s C x hx
  rw [hclsy] at hall
  exact (D.act_pi_cls_eq_iff hd C
    (fun n ↦ natU U n s * x n * (natU U n s)ᴴ) hy (iota γ)).mp (hall γ)

end UltraproductAdjointModel

/-! ## The printed proof of `thm:kazhdan-transport` -/

/-- **KT.24.**  The class `ξ = [ξ_n]_ω` is well defined, and this is the one
place the *operator-norm* bound on `(x_n)` is used: it gives the normalized
Hilbert--Schmidt bound that the numerator of `K_ω` asks for.  The manuscript
uses it in exactly this position and for exactly this purpose. -/
theorem hsNormSq_le_of_opNorm_le {d : ℕ → ℕ} (hd : ∀ n, 0 < d n)
    (x : ∀ n, NatMatrix d n) {M : ℝ} (hM : ∀ n, ‖x n‖ ≤ M) (n : ℕ) :
    hsNormSq (naturalFiniteModel (d n)) (x n) ≤ M * M :=
  le_trans (hsNormSq_le_mul_self_l2_opNorm _ (by simpa using hd n) (x n))
    (mul_self_le_mul_self (norm_nonneg _) (hM n))

/-- **Kazhdan transport, by the manuscript's ultraproduct proof.**

`non_mf_groups_exist.tex`, `\label{thm:kazhdan-transport}` and the proof
printed under it.  Given the ambient of steps
KT.01--KT.09 for every free ultrafilter on `ℕ`, the printed contradiction
runs: if the conclusion fails there are `γ₀`, `δ > 0` and an infinite
`I ⊆ ℕ` on which the conjugated commutator has normalized Hilbert--Schmidt
norm at least `δ`; a free ultrafilter `ω` with `I ∈ ω` is fixed; KT.11 makes
the conjugated commutators vanish along `ω`; and `I ∈ ω` is contradicted.
Since the failing subsequence was arbitrary, the full sequence converges.

The uniform **operator-norm** bound on `(x_n)` is used exactly where the
manuscript uses it -- to make the class `ξ = [ξ_n]_ω` well defined -- via
`hsNormSq_le_mul_self_l2_opNorm`.

`ambient` is discharged by
`UltraproductModelConstruction.ultraproductAdjointModel`, which builds the
KT.01--KT.09 bundle at every free ultrafilter out of property `(T)`, the
compression, positive dimensions and asymptotic multiplicativity -- that is,
out of the hypotheses of `thm:kazhdan-transport` and nothing else.  The badged
statement of the theorem,
`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`, is proved through this
declaration, so the printed proof is the one its badge certifies. -/
theorem ultraproductKazhdanTransport
    {Γ : Type} {H : Type*} [Group Γ] [Group H]
    (iota : Γ →* H) (s : H) (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (x : ∀ n, NatMatrix d n)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
    (hx : ∀ γ : Γ, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      Real.sqrt (hsNormSq (naturalFiniteModel (d n))
        (x n * natU U n (iota γ) - natU U n (iota γ) * x n)) ≤ ε)
    (ambient : ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
      UltraproductAdjointModel iota s d U ω) :
    ∀ γ : Γ, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      Real.sqrt (hsNormSq (naturalFiniteModel (d n))
        ((natU U n s * x n * (natU U n s)ᴴ) * natU U n (iota γ)
          - natU U n (iota γ) * (natU U n s * x n * (natU U n s)ᴴ))) ≤ ε := by
  obtain ⟨M, _hM0, hMle⟩ := hbound
  have hcard : ∀ n, 0 < Fintype.card (naturalFiniteModel (d n)) := fun n ↦ by
    simpa using hd n
  -- the operator-norm bound gives the Hilbert--Schmidt bound `ξ` needs
  have hxb : ∀ n, hsNormSq (naturalFiniteModel (d n)) (x n) ≤ M * M :=
    hsNormSq_le_of_opNorm_le hd x hMle
  have hxtend : ∀ γ : Γ, Filter.Tendsto
      (fun n ↦ hsNormSq (naturalFiniteModel (d n))
        (x n * natU U n (iota γ) - natU U n (iota γ) * x n))
      Filter.atTop (nhds 0) := fun γ ↦
    tendsto_of_sqrt_le (fun n ↦ hsNormSq_nonneg _ _) (hx γ)
  -- The printed proof is by contradiction, and this is its opening sentence.
  by_contra hfail
  obtain ⟨γ₀, δ, hδ, hinf⟩ :=
    PrintedTransportOpening.exists_gamma_infinite_commutator_defect d U x iota s
      hfail
  -- `natU` is reducibly the coercion, so the bad set is the same set written
  -- in the spelling `kt_11_descend` uses.
  have hinf' : {n : ℕ | δ ≤ Real.sqrt (hsNormSq (naturalFiniteModel (d n))
      ((natU U n s * x n * (natU U n s)ᴴ) * natU U n (iota γ₀)
        - natU U n (iota γ₀) * (natU U n s * x n * (natU U n s)ᴴ)))}.Infinite :=
    hinf
  -- "Fix a free ultrafilter `ω` on `ℕ` with `I ∈ ω`."
  obtain ⟨ω, hIω, hωcof⟩ := UltrafilterLimit.exists_freeUltrafilter_mem hinf'
  have hωtop : (ω : Filter ℕ) ≤ Filter.atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact hωcof
  -- KT.11 makes the conjugated commutators vanish along `ω`.
  have hvanish := (ambient ω hωcof).kt_11_descend hd (M * M) x hxb
    (fun γ' ↦ (hxtend γ').mono_left hωtop) γ₀
  have hsmall : ∀ᶠ n in (ω : Filter ℕ),
      hsNormSq (naturalFiniteModel (d n))
        ((natU U n s * x n * (natU U n s)ᴴ) * natU U n (iota γ₀)
          - natU U n (iota γ₀) * (natU U n s * x n * (natU U n s)ᴴ)) < δ ^ 2 := by
    have h := Metric.tendsto_nhds.mp hvanish (δ ^ 2) (by positivity)
    filter_upwards [h] with n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hsNormSq_nonneg _ _)] at hn
  -- and `I ∈ ω` says it is bounded below there, which is the contradiction.
  have hbig : ∀ᶠ n in (ω : Filter ℕ),
      δ ≤ Real.sqrt (hsNormSq (naturalFiniteModel (d n))
        ((natU U n s * x n * (natU U n s)ᴴ) * natU U n (iota γ₀)
          - natU U n (iota γ₀) * (natU U n s * x n * (natU U n s)ᴴ))) := hIω
  obtain ⟨n, hnbig, hnsmall⟩ := (hbig.and hsmall).exists
  have hsq : δ ^ 2 ≤ hsNormSq (naturalFiniteModel (d n))
      ((natU U n s * x n * (natU U n s)ᴴ) * natU U n (iota γ₀)
        - natU U n (iota γ₀) * (natU U n s * x n * (natU U n s)ᴴ)) := by
    calc δ ^ 2 ≤ (Real.sqrt (hsNormSq (naturalFiniteModel (d n))
            ((natU U n s * x n * (natU U n s)ᴴ) * natU U n (iota γ₀)
              - natU U n (iota γ₀)
                * (natU U n s * x n * (natU U n s)ᴴ)))) ^ 2 :=
          (sq_le_sq₀ hδ.le (Real.sqrt_nonneg _)).2 hnbig
      _ = _ := Real.sq_sqrt (hsNormSq_nonneg _ _)
  linarith

end GroupApproximation
