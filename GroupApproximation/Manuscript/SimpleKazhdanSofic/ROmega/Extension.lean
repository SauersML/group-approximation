import GroupApproximation.Manuscript.SimpleKazhdanSofic.ROmega.Resolvent
import Mathlib.Tactic.Module
import GroupApproximation.Meta.AxiomGuard

/-!
# `L(G) ↪ R^ω`: extending a trace-preserving `⋆`-homomorphism from a dense graph

`simple_kazhdan_sofic_group.tex`:

> (tex 345–348) … and $L(G)$ embeds in $\mathcal R^\omega$.
>
> (tex 350–355) … $L(G)\mathbin{\bar\otimes}\mathcal R$ … embeds in $\mathcal R^\omega$.

Step 3 of the route described in `ROmega/TwoNorm`.  Let `M` be a von Neumann algebra with a
separating tracial vector `ξ`, and let `Gr ⊆ M × N^ω` be a `⋆`-subalgebra (a *graph*) with
`trω(p₂) = ⟪ξ, p₁ ξ⟫` for `p ∈ Gr`, whose first coordinates are `‖·ξ‖`-dense in `M`.

* `Rel T v`: `(T, v)` is approximated by elements `p ∈ Gr` with `‖p₁‖` and a representative of
  `p₂` uniformly bounded, `‖(p₁ − T) ξ‖` and `‖p₂ − v‖₂` small.  Traciality gives
  `‖p₂‖₂ = ‖p₁ ξ‖` on `Gr`, so `Rel` is a function, and it is closed under `+`, `⋆`, scalars,
  and products (with `T ∈ M`).
* Every self-adjoint `S = q(g(S))`, `‖S‖ ≤ 1/2`, is related to something: approximate `g(S)` by
  self-adjoint `pₖ ∈ Gr`, pass to `q(pₖ)`, which is `2`-norm Cauchy with uniform bound `1/2`, take
  the diagonal limit (`exists_limit`), and approximate `q` by polynomials to stay inside `Gr` with
  bounds.
* Scaling and `T = Re T + i Im T` give `Rel T (Φ T)` for every `T ∈ M`, and `Φ` is an injective
  trace-preserving `⋆`-homomorphism extending the graph.
-/

namespace GroupApproximation.SimpleKazhdanSofic.ROmega

open Filter TracialUltrapower
open scoped InnerProductSpace Topology

noncomputable section

universe v

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialVector M)
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {N : VonNeumannAlgebra K} {σ : TracialVector N} {ω : Ultrafilter ℕ}
variable (Gr : StarSubalgebra ℂ ((H →L[ℂ] H) × Ultrapower σ ω))

/-- `(T, v)` lies in the bounded closure of the graph `Gr`. -/
def Rel (T : H →L[ℂ] H) (v : Ultrapower σ ω) : Prop :=
  ∃ B : ℝ, ∀ ε > 0, ∃ p ∈ Gr, ‖p.1‖ ≤ B ∧
    (∃ a : boundedSeq N, mk σ ω a = p.2 ∧ ∀ n, ‖(a : ℕ → (K →L[ℂ] K)) n‖ ≤ B) ∧
    ‖(p.1 - T) τ.vec‖ < ε ∧ twoNorm σ ω (p.2 - v) < ε

/-- On a trace-preserving graph, `‖p₂‖₂ = ‖p₁ ξ‖`. -/
theorem twoNorm_graph (htr : ∀ p ∈ Gr, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ)
    {p : (H →L[ℂ] H) × Ultrapower σ ω} (hp : p ∈ Gr) : twoNorm σ ω p.2 = ‖p.1 τ.vec‖ := by
  have h := htr (star p * p) (mul_mem (star_mem hp) hp)
  rw [Prod.snd_mul, Prod.snd_star, Prod.fst_mul, Prod.fst_star, τ.inner_star_mul_self] at h
  rw [twoNorm, h, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg _)]

theorem twoNorm_sub_graph (htr : ∀ p ∈ Gr, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ)
    {p q : (H →L[ℂ] H) × Ultrapower σ ω} (hp : p ∈ Gr) (hq : q ∈ Gr) :
    twoNorm σ ω (p.2 - q.2) = ‖(p.1 - q.1) τ.vec‖ := by
  have h := twoNorm_graph τ Gr htr (sub_mem hp hq)
  rwa [Prod.snd_sub, Prod.fst_sub] at h

theorem rel_of_mem {p : (H →L[ℂ] H) × Ultrapower σ ω} (hp : p ∈ Gr) : Rel τ Gr p.1 p.2 := by
  obtain ⟨a, ha⟩ := mk_surjective σ ω p.2
  obtain ⟨C, hC⟩ := exists_bound a
  refine ⟨max ‖p.1‖ C, fun ε hε ↦ ⟨p, hp, le_max_left _ _,
    ⟨a, ha, fun n ↦ (hC n).trans (le_max_right _ _)⟩, ?_, ?_⟩⟩
  · rw [sub_self, _root_.zero_apply, norm_zero]
    exact hε
  · rw [sub_self, twoNorm_zero]
    exact hε

theorem rel_one : Rel τ Gr 1 1 :=
  rel_of_mem τ Gr (one_mem Gr)

theorem rel_zero : Rel τ Gr 0 0 :=
  rel_of_mem τ Gr (zero_mem Gr)

theorem rel_algebraMap (c : ℂ) :
    Rel τ Gr (algebraMap ℂ (H →L[ℂ] H) c) (algebraMap ℂ (Ultrapower σ ω) c) :=
  rel_of_mem τ Gr (Gr.algebraMap_mem c)

/-- **`Rel` is a function.** -/
theorem rel_unique (htr : ∀ p ∈ Gr, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ)
    {T : H →L[ℂ] H} {v w : Ultrapower σ ω} (h1 : Rel τ Gr T v) (h2 : Rel τ Gr T w) : v = w := by
  refine eq_of_twoNorm_sub_le σ ω fun ε hε ↦ ?_
  obtain ⟨-, h1⟩ := h1
  obtain ⟨-, h2⟩ := h2
  obtain ⟨p, hp, -, -, hpT, hpv⟩ := h1 (ε / 4) (by linarith)
  obtain ⟨q, hq, -, -, hqT, hqw⟩ := h2 (ε / 4) (by linarith)
  have hpq : twoNorm σ ω (p.2 - q.2) < ε / 2 := by
    rw [twoNorm_sub_graph τ Gr htr hp hq]
    calc ‖(p.1 - q.1) τ.vec‖ = ‖(p.1 - T) τ.vec - (q.1 - T) τ.vec‖ := by
          rw [← _root_.sub_apply, sub_sub_sub_cancel_right]
      _ ≤ ‖(p.1 - T) τ.vec‖ + ‖(q.1 - T) τ.vec‖ := norm_sub_le _ _
      _ < ε / 2 := by linarith
  have e1 := twoNorm_sub_le σ ω v p.2 w
  have e2 := twoNorm_sub_le σ ω p.2 q.2 w
  rw [twoNorm_sub_comm σ ω v p.2] at e1
  linarith

theorem rel_add {T S : H →L[ℂ] H} {v w : Ultrapower σ ω} (h1 : Rel τ Gr T v)
    (h2 : Rel τ Gr S w) : Rel τ Gr (T + S) (v + w) := by
  obtain ⟨B, h1⟩ := h1
  obtain ⟨B', h2⟩ := h2
  refine ⟨B + B', fun ε hε ↦ ?_⟩
  obtain ⟨p, hp, hpB, ⟨a, ha, haB⟩, hpT, hpv⟩ := h1 (ε / 2) (by linarith)
  obtain ⟨q, hq, hqB, ⟨b, hb, hbB⟩, hqS, hqw⟩ := h2 (ε / 2) (by linarith)
  refine ⟨p + q, add_mem hp hq, ?_, ⟨a + b, ?_, fun n ↦ ?_⟩, ?_, ?_⟩
  · rw [Prod.fst_add]
    exact (norm_add_le _ _).trans (add_le_add hpB hqB)
  · rw [map_add, ha, hb, Prod.snd_add]
  · show ‖(a : ℕ → (K →L[ℂ] K)) n + (b : ℕ → (K →L[ℂ] K)) n‖ ≤ B + B'
    exact (norm_add_le _ _).trans (add_le_add (haB n) (hbB n))
  · rw [Prod.fst_add, add_sub_add_comm, _root_.add_apply]
    exact (norm_add_le _ _).trans_lt (by linarith)
  · rw [Prod.snd_add, add_sub_add_comm]
    exact (twoNorm_add_le σ ω _ _).trans_lt (by linarith)

/-- `B x + C y < ε` once `x S, y S < ε` and `B + C < S`. -/
theorem mul_add_mul_lt {B C S x y ε : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hS : B + C < S)
    (hε : 0 < ε) (hx : x * S < ε) (hy : y * S < ε) : B * x + C * y < ε := by
  have hSpos : 0 < S := by linarith
  have h1 : B * (x * S) ≤ B * ε := mul_le_mul_of_nonneg_left hx.le hB
  have h2 : C * (y * S) ≤ C * ε := mul_le_mul_of_nonneg_left hy.le hC
  have h3 : (B + C) * ε < S * ε := mul_lt_mul_of_pos_right hS hε
  by_contra hcon
  push Not at hcon
  have h4 : ε * S ≤ (B * x + C * y) * S := mul_le_mul_of_nonneg_right hcon hSpos.le
  nlinarith

/-- **Products.** -/
theorem rel_mul (hGM : ∀ p ∈ Gr, p.1 ∈ M) {T S : H →L[ℂ] H} {v w : Ultrapower σ ω}
    (hTM : T ∈ M) (hT : Rel τ Gr T v) (hS : Rel τ Gr S w) : Rel τ Gr (T * S) (v * w) := by
  obtain ⟨B, hT⟩ := hT
  obtain ⟨B', hS⟩ := hS
  obtain ⟨p₀, -, hp₀B, -⟩ := hT 1 one_pos
  obtain ⟨q₀, -, hq₀B, -⟩ := hS 1 one_pos
  have hB : 0 ≤ B := (norm_nonneg _).trans hp₀B
  have hB' : 0 ≤ B' := (norm_nonneg _).trans hq₀B
  obtain ⟨c, rfl⟩ := mk_surjective σ ω v
  obtain ⟨Cv, hCv⟩ := exists_bound c
  have hCv0 : 0 ≤ Cv := (norm_nonneg _).trans (hCv 0)
  have hTn := norm_nonneg T
  have hpos : 0 < B' + ‖T‖ + Cv + 1 := by linarith
  refine ⟨B * B', fun ε hε ↦ ?_⟩
  obtain ⟨p, hp, hpB, ⟨a, ha, haB⟩, hpT, hpv⟩ := hT (ε / (B' + ‖T‖ + Cv + 1)) (div_pos hε hpos)
  obtain ⟨q, hq, hqB, ⟨b, hb, hbB⟩, hqS, hqw⟩ := hS (ε / (B' + ‖T‖ + Cv + 1)) (div_pos hε hpos)
  rw [lt_div_iff₀ hpos] at hpT hpv hqS hqw
  refine ⟨p * q, mul_mem hp hq, ?_, ⟨a * b, ?_, fun n ↦ ?_⟩, ?_, ?_⟩
  · rw [Prod.fst_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul hpB hqB (norm_nonneg _) hB)
  · rw [map_mul, ha, hb, Prod.snd_mul]
  · show ‖(a : ℕ → (K →L[ℂ] K)) n * (b : ℕ → (K →L[ℂ] K)) n‖ ≤ B * B'
    exact (norm_mul_le _ _).trans (mul_le_mul (haB n) (hbB n) (norm_nonneg _) hB)
  · have e : (p * q).1 - T * S = (p.1 - T) * q.1 + T * (q.1 - S) := by
      rw [Prod.fst_mul]
      noncomm_ring
    rw [e, _root_.add_apply]
    refine (norm_add_le _ _).trans_lt ?_
    have h1 : ‖((p.1 - T) * q.1) τ.vec‖ ≤ B' * ‖(p.1 - T) τ.vec‖ :=
      (τ.norm_mul_apply_le (sub_mem (hGM p hp) hTM) (hGM q hq)).trans
        (mul_le_mul_of_nonneg_right hqB (norm_nonneg _))
    have h2 : ‖(T * (q.1 - S)) τ.vec‖ ≤ ‖T‖ * ‖(q.1 - S) τ.vec‖ := by
      rw [mul_apply_eq_comp]
      exact T.le_opNorm _
    have h3 := mul_add_mul_lt hB' hTn (by linarith : B' + ‖T‖ < B' + ‖T‖ + Cv + 1) hε hpT hqS
    linarith
  · have e : (p * q).2 - mk σ ω c * w = (p.2 - mk σ ω c) * mk σ ω b + mk σ ω c * (q.2 - w) := by
      rw [Prod.snd_mul, ← hb]
      noncomm_ring
    rw [e]
    refine (twoNorm_add_le σ ω _ _).trans_lt ?_
    have h1 := twoNorm_mul_mk_le σ ω hbB (p.2 - mk σ ω c)
    have h2 := twoNorm_mk_mul_le σ ω hCv (q.2 - w)
    have h3 := mul_add_mul_lt hB' hCv0 (by linarith : B' + Cv < B' + ‖T‖ + Cv + 1) hε hpv hqw
    linarith

/-- **Adjoints.** -/
theorem rel_star (hGM : ∀ p ∈ Gr, p.1 ∈ M) {T : H →L[ℂ] H} {v : Ultrapower σ ω} (hTM : T ∈ M)
    (h : Rel τ Gr T v) : Rel τ Gr (star T) (star v) := by
  obtain ⟨B, h⟩ := h
  refine ⟨B, fun ε hε ↦ ?_⟩
  obtain ⟨p, hp, hpB, ⟨a, ha, haB⟩, hpT, hpv⟩ := h ε hε
  refine ⟨star p, star_mem hp, ?_, ⟨star a, ?_, fun n ↦ ?_⟩, ?_, ?_⟩
  · rw [Prod.fst_star, norm_star]
    exact hpB
  · rw [← star_mk, ha, Prod.snd_star]
  · show ‖star ((a : ℕ → (K →L[ℂ] K)) n)‖ ≤ B
    rw [norm_star]
    exact haB n
  · rw [Prod.fst_star, ← star_sub, τ.norm_star_apply (sub_mem (hGM p hp) hTM)]
    exact hpT
  · rw [Prod.snd_star, ← star_sub, twoNorm_star]
    exact hpv

/-- **The trace is preserved.** -/
theorem rel_trace (htr : ∀ p ∈ Gr, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ)
    {T : H →L[ℂ] H} {v : Ultrapower σ ω} (h : Rel τ Gr T v) :
    ultratrace σ ω v = ⟪τ.vec, T τ.vec⟫_ℂ := by
  obtain ⟨-, h⟩ := h
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  obtain ⟨p, hp, -, -, hpT, hpv⟩ := h (ε / 2) (by linarith)
  rw [dist_eq_norm]
  have e : ultratrace σ ω v - ⟪τ.vec, T τ.vec⟫_ℂ =
      ⟪τ.vec, (p.1 - T) τ.vec⟫_ℂ - ultratrace σ ω (p.2 - v) := by
    rw [map_sub, htr p hp, _root_.sub_apply, inner_sub_right]
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := τ.norm_inner_apply_le_norm_apply (p.1 - T)
  have h2 := norm_ultratrace_le_twoNorm σ ω (p.2 - v)
  linarith

/-- **Scalars.** -/
theorem rel_smul (hGM : ∀ p ∈ Gr, p.1 ∈ M) (c : ℂ) {T : H →L[ℂ] H} {v : Ultrapower σ ω}
    (h : Rel τ Gr T v) : Rel τ Gr (c • T) (c • v) := by
  have h' := rel_mul τ Gr hGM (M.toStarSubalgebra.algebraMap_mem c) (rel_algebraMap τ Gr c) h
  rwa [← Algebra.smul_def, ← Algebra.smul_def] at h'

theorem coord_polyEval (c : ℕ → ℂ) (m : ℕ) (r : boundedSeq N) (n : ℕ) :
    ((polyEval c m r : boundedSeq N) : ℕ → (K →L[ℂ] K)) n =
      polyEval c m ((r : ℕ → (K →L[ℂ] K)) n) := by
  have h1 : ((polyEval c m r : boundedSeq N) : ℕ → (K →L[ℂ] K)) =
      polyEval c m (r : ℕ → (K →L[ℂ] K)) :=
    map_polyEval (boundedSeq N).subtype c m r
  have h2 : polyEval c m (r : ℕ → (K →L[ℂ] K)) n = polyEval c m ((r : ℕ → (K →L[ℂ] K)) n) :=
    map_polyEval (Pi.evalAlgHom ℂ (fun _ : ℕ ↦ K →L[ℂ] K) n) c m (r : ℕ → (K →L[ℂ] K))
  rw [h1]
  exact h2

/-! ### Self-adjoint approximants -/

theorem isSelfAdjoint_half : IsSelfAdjoint (2⁻¹ : ℂ) :=
  isSelfAdjoint_iff.mpr (by rw [star_inv₀, star_ofNat])

/-- Dense self-adjoint graph elements with self-adjoint representatives. -/
theorem exists_sa_approx (hGM : ∀ p ∈ Gr, p.1 ∈ M)
    (hdense : ∀ T ∈ M, ∀ ε > 0, ∃ p ∈ Gr, ‖(p.1 - T) τ.vec‖ < ε) {S : H →L[ℂ] H} (hSM : S ∈ M)
    (hS : IsSelfAdjoint S) {ε : ℝ} (hε : 0 < ε) :
    ∃ (p : (H →L[ℂ] H) × Ultrapower σ ω) (r : boundedSeq N), p ∈ Gr ∧ IsSelfAdjoint p.1 ∧
      (∀ n, IsSelfAdjoint ((r : ℕ → (K →L[ℂ] K)) n)) ∧ mk σ ω r = p.2 ∧
      ‖(p.1 - S) τ.vec‖ < ε := by
  obtain ⟨p, hp, hpS⟩ := hdense S hSM ε hε
  obtain ⟨a, ha⟩ := mk_surjective σ ω p.2
  refine ⟨(2⁻¹ : ℂ) • (p + star p), (2⁻¹ : ℂ) • (a + star a),
    Gr.smul_mem (add_mem hp (star_mem hp)) _, ?_, fun n ↦ ?_, ?_, ?_⟩
  · rw [Prod.smul_fst, Prod.fst_add, Prod.fst_star]
    exact isSelfAdjoint_half.smul (IsSelfAdjoint.add_star_self _)
  · show IsSelfAdjoint
      ((2⁻¹ : ℂ) • ((a : ℕ → (K →L[ℂ] K)) n + star ((a : ℕ → (K →L[ℂ] K)) n)))
    exact isSelfAdjoint_half.smul (IsSelfAdjoint.add_star_self _)
  · rw [mk_smul, map_add, ← star_mk, ha, Prod.smul_snd, Prod.snd_add, Prod.snd_star]
  · have e : (2⁻¹ : ℂ) • (p.1 + star p.1) - S = (2⁻¹ : ℂ) • ((p.1 - S) + star (p.1 - S)) := by
      rw [star_sub, hS.star_eq]
      module
    rw [Prod.smul_fst, Prod.fst_add, Prod.fst_star, e, _root_.smul_apply, norm_smul,
      _root_.add_apply, norm_inv, Complex.norm_two]
    have h1 : ‖(star (p.1 - S)) τ.vec‖ = ‖(p.1 - S) τ.vec‖ :=
      τ.norm_star_apply (sub_mem (hGM p hp) hSM)
    have h2 := norm_add_le ((p.1 - S) τ.vec) ((star (p.1 - S)) τ.vec)
    linarith

/-- `‖x‖ ≤ 1` once `x` is `1/2`-close to something of norm `≤ 1/2`. -/
theorem norm_le_one_of_near {E : Type*} [SeminormedAddCommGroup E] {x y : E} {η : ℝ}
    (hxy : ‖x - y‖ ≤ min η (1 / 2)) (hy : ‖y‖ ≤ 1 / 2) : ‖x‖ ≤ 1 := by
  have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  have h2 := min_le_right η (1 / 2 : ℝ)
  linarith

/-- Polynomials in a graph element approximate `q` of it, with uniform bound `1`. -/
theorem exists_poly_near {p : (H →L[ℂ] H) × Ultrapower σ ω} (hp : p ∈ Gr) {r : boundedSeq N}
    (hpsa : IsSelfAdjoint p.1) (hrsa : ∀ n, IsSelfAdjoint ((r : ℕ → (K →L[ℂ] K)) n))
    (hmk : mk σ ω r = p.2) {η : ℝ} (hη : 0 < η) :
    ∃ p' ∈ Gr, ‖p'.1‖ ≤ 1 ∧
      (∃ a : boundedSeq N, mk σ ω a = p'.2 ∧ ∀ n, ‖(a : ℕ → (K →L[ℂ] K)) n‖ ≤ 1) ∧
      ‖p'.1 - cfc qfun p.1‖ ≤ η ∧ twoNorm σ ω (p'.2 - mk σ ω (qseq r)) ≤ η := by
  obtain ⟨C, hC⟩ := exists_bound r
  obtain ⟨cc, m, hA, hB⟩ := exists_poly_approx (A := H →L[ℂ] H) (B := K →L[ℂ] K)
    (max ‖p.1‖ C) (min η (1 / 2)) (lt_min hη (by norm_num))
  have hfst : (polyEval cc m p).1 = polyEval cc m p.1 :=
    map_polyEval (AlgHom.fst ℂ (H →L[ℂ] H) (Ultrapower σ ω)) cc m p
  have hsnd : (polyEval cc m p).2 = polyEval cc m p.2 :=
    map_polyEval (AlgHom.snd ℂ (H →L[ℂ] H) (Ultrapower σ ω)) cc m p
  have hmk' : mk σ ω (polyEval cc m r) = (polyEval cc m p).2 := by
    rw [hsnd, ← hmk]
    exact map_polyEval (mkStarAlgHom σ ω) cc m r
  have hB' : ∀ n, ‖((polyEval cc m r : boundedSeq N) : ℕ → (K →L[ℂ] K)) n -
      (qseq r : ℕ → (K →L[ℂ] K)) n‖ ≤ min η (1 / 2) := fun n ↦ by
    rw [coord_polyEval, qseq_apply]
    exact hB _ (hrsa n) ((hC n).trans (le_max_right _ _))
  have hA' : ‖polyEval cc m p.1 - cfc qfun p.1‖ ≤ min η (1 / 2) :=
    hA _ hpsa (le_max_left _ _)
  refine ⟨polyEval cc m p, polyEval_mem hp cc m, ?_, ⟨polyEval cc m r, hmk', fun n ↦ ?_⟩, ?_, ?_⟩
  · rw [hfst]
    exact norm_le_one_of_near hA' (norm_cfc_qfun_le p.1)
  · exact norm_le_one_of_near (hB' n) (norm_qseq_le r n)
  · rw [hfst]
    exact hA'.trans (min_le_left _ _)
  · rw [← hmk']
    exact (twoNorm_mk_sub_le σ ω hB').trans (min_le_left _ _)

/-! ### The resolvent limit -/

/-- `q` of self-adjoint approximants of `S` is `2`-norm Cauchy. -/
theorem twoNorm_qseq_cauchy (htr : ∀ p ∈ Gr, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ)
    {S : H →L[ℂ] H} {p : ℕ → (H →L[ℂ] H) × Ultrapower σ ω} (hp : ∀ k, p k ∈ Gr)
    {r : ℕ → boundedSeq N} (hrsa : ∀ k n, IsSelfAdjoint ((r k : ℕ → (K →L[ℂ] K)) n))
    (hmk : ∀ k, mk σ ω (r k) = (p k).2)
    (hclose : ∀ k, ‖((p k).1 - S) τ.vec‖ < 1 / ((k : ℝ) + 1)) (i j : ℕ) (hij : i ≤ j) :
    twoNorm σ ω (mk σ ω (qseq (r j)) - mk σ ω (qseq (r i))) < 5 * (1 / ((i : ℝ) + 1)) := by
  have hij' : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
  have hji : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
    gcongr
  have hcl : ‖((p j).1 - (p i).1) τ.vec‖ < 2 * (1 / ((i : ℝ) + 1)) := by
    calc ‖((p j).1 - (p i).1) τ.vec‖ = ‖((p j).1 - S) τ.vec - ((p i).1 - S) τ.vec‖ := by
          rw [← _root_.sub_apply, sub_sub_sub_cancel_right]
      _ ≤ ‖((p j).1 - S) τ.vec‖ + ‖((p i).1 - S) τ.vec‖ := norm_sub_le _ _
      _ < 2 * (1 / ((i : ℝ) + 1)) := by
          have h1 := hclose j
          have h2 := hclose i
          linarith
  have h1 := twoNorm_mk_qseq_sub_le σ ω (hrsa j) (hrsa i)
  rw [hmk, hmk, twoNorm_sub_graph τ Gr htr (hp j) (hp i)] at h1
  have h3 : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
  linarith

/-- **Self-adjoint `q(S)` is related to something.** -/
theorem exists_rel_qfun (hω : (ω : Filter ℕ) ≤ cofinite) (hGM : ∀ p ∈ Gr, p.1 ∈ M)
    (htr : ∀ p ∈ Gr, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ)
    (hdense : ∀ T ∈ M, ∀ ε > 0, ∃ p ∈ Gr, ‖(p.1 - T) τ.vec‖ < ε) {S : H →L[ℂ] H} (hSM : S ∈ M)
    (hS : IsSelfAdjoint S) : ∃ v, Rel τ Gr (cfc qfun S) v := by
  choose p r hp hpsa hrsa hmk hclose using fun k : ℕ ↦
    exists_sa_approx τ Gr hGM hdense hSM hS (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
  obtain ⟨c, -, hcd⟩ := exists_limit σ ω hω (fun k ↦ qseq (r k))
    (fun k n ↦ norm_qseq_le (r k) n) (fun i ↦ 5 * (1 / ((i : ℝ) + 1)))
    (twoNorm_qseq_cauchy τ Gr htr hp hrsa hmk hclose)
  refine ⟨mk σ ω c, 1, fun ε hε ↦ ?_⟩
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < ε / 10)
  obtain ⟨p', hp', hp'B, hp'a, hp'1, hp'2⟩ :=
    exists_poly_near Gr (hp k) (hpsa k) (hrsa k) (hmk k) (by linarith : (0 : ℝ) < ε / 4)
  refine ⟨p', hp', hp'B, hp'a, ?_, ?_⟩
  · have e : (p'.1 - cfc qfun S) τ.vec =
        (p'.1 - cfc qfun (p k).1) τ.vec + (cfc qfun (p k).1 - cfc qfun S) τ.vec := by
      rw [← _root_.add_apply, sub_add_sub_cancel]
    rw [e]
    have h1 := (τ.norm_apply_le (p'.1 - cfc qfun (p k).1)).trans hp'1
    have h2 := norm_qfun_sub_apply_le τ (hGM _ (hp k)) hSM (hpsa k) hS
    have h3 := hclose k
    refine (norm_add_le _ _).trans_lt ?_
    linarith
  · have h1 := twoNorm_sub_le σ ω p'.2 (mk σ ω (qseq (r k))) (mk σ ω c)
    have h2 : twoNorm σ ω (mk σ ω (qseq (r k)) - mk σ ω c) ≤ 5 * (1 / ((k : ℝ) + 1)) := by
      rw [twoNorm_sub_comm σ ω]
      exact hcd k
    linarith

theorem exists_rel_sa_small (hω : (ω : Filter ℕ) ≤ cofinite) (hGM : ∀ p ∈ Gr, p.1 ∈ M)
    (htr : ∀ p ∈ Gr, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ)
    (hdense : ∀ T ∈ M, ∀ ε > 0, ∃ p ∈ Gr, ‖(p.1 - T) τ.vec‖ < ε) {T : H →L[ℂ] H} (hTM : T ∈ M)
    (hT : IsSelfAdjoint T) (hTn : ‖T‖ ≤ 1 / 2) : ∃ v, Rel τ Gr T v := by
  have h := exists_rel_qfun τ Gr hω hGM htr hdense (cfc_mem hTM gfun) (cfc_predicate gfun T)
  rwa [cfc_qfun_cfc_gfun T hT hTn] at h

/-- **Every self-adjoint element of `M` is related to something** (by scaling). -/
theorem exists_rel_sa (hω : (ω : Filter ℕ) ≤ cofinite) (hGM : ∀ p ∈ Gr, p.1 ∈ M)
    (htr : ∀ p ∈ Gr, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ)
    (hdense : ∀ T ∈ M, ∀ ε > 0, ∃ p ∈ Gr, ‖(p.1 - T) τ.vec‖ < ε) {X : H →L[ℂ] H} (hXM : X ∈ M)
    (hX : IsSelfAdjoint X) : ∃ v, Rel τ Gr X v := by
  obtain ⟨n, hn⟩ := exists_nat_ge (2 * ‖X‖)
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmC : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
  have hsa : IsSelfAdjoint ((n : ℂ) + 1)⁻¹ :=
    isSelfAdjoint_iff.mpr (by rw [star_inv₀, star_add, star_natCast, star_one])
  have hsmall : ‖((n : ℂ) + 1)⁻¹ • X‖ ≤ 1 / 2 := by
    rw [norm_smul, norm_inv, hnorm, inv_mul_le_iff₀ hm]
    have hX0 := norm_nonneg X
    linarith
  obtain ⟨v, hv⟩ := exists_rel_sa_small τ Gr hω hGM htr hdense
    (M.toStarSubalgebra.smul_mem hXM ((n : ℂ) + 1)⁻¹) (hsa.smul hX) hsmall
  have h := rel_smul τ Gr hGM ((n : ℂ) + 1) hv
  rw [smul_smul, mul_inv_cancel₀ hmC, one_smul] at h
  exact ⟨_, h⟩

/-- **Every element of `M` is related to something**: `T = Re T + i Im T`. -/
theorem exists_rel (hω : (ω : Filter ℕ) ≤ cofinite) (hGM : ∀ p ∈ Gr, p.1 ∈ M)
    (htr : ∀ p ∈ Gr, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ)
    (hdense : ∀ T ∈ M, ∀ ε > 0, ∃ p ∈ Gr, ‖(p.1 - T) τ.vec‖ < ε) {T : H →L[ℂ] H}
    (hTM : T ∈ M) : ∃ v, Rel τ Gr T v := by
  have hXM : (2⁻¹ : ℂ) • (T + star T) ∈ M :=
    M.toStarSubalgebra.smul_mem (add_mem hTM (star_mem hTM)) _
  have hYM : (2⁻¹ : ℂ) • (Complex.I • (star T - T)) ∈ M :=
    M.toStarSubalgebra.smul_mem (M.toStarSubalgebra.smul_mem (sub_mem (star_mem hTM) hTM) _) _
  have hYsa : IsSelfAdjoint ((2⁻¹ : ℂ) • (Complex.I • (star T - T))) := by
    refine isSelfAdjoint_half.smul (isSelfAdjoint_iff.mpr ?_)
    rw [star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg,
      neg_sub]
  obtain ⟨v, hv⟩ := exists_rel_sa τ Gr hω hGM htr hdense hXM
    (isSelfAdjoint_half.smul (IsSelfAdjoint.add_star_self T))
  obtain ⟨w, hw⟩ := exists_rel_sa τ Gr hω hGM htr hdense hYM hYsa
  have hIw := rel_smul τ Gr hGM Complex.I hw
  have e1 : Complex.I • ((2⁻¹ : ℂ) • (Complex.I • (star T - T))) = (2⁻¹ : ℂ) • (T - star T) := by
    rw [smul_comm Complex.I (2⁻¹ : ℂ), smul_smul Complex.I Complex.I, Complex.I_mul_I,
      neg_one_smul, neg_sub]
  rw [e1] at hIw
  have h := rel_add τ Gr hv hIw
  have e2 : (2⁻¹ : ℂ) • (T + star T) + (2⁻¹ : ℂ) • (T - star T) = T := by
    module
  rw [e2] at h
  exact ⟨_, h⟩

/-! ### The extension -/

/-- **Extension from a dense trace-preserving graph.**  If `Gr ⊆ M × N^ω` is a `⋆`-subalgebra with
`trω(p₂) = ⟪ξ, p₁ ξ⟫` whose first coordinates are `‖·ξ‖`-dense in `M`, and `ξ` is separating, then
there is an injective trace-preserving `⋆`-homomorphism `M → N^ω` extending the graph. -/
theorem exists_extension (hω : (ω : Filter ℕ) ≤ cofinite) (hGM : ∀ p ∈ Gr, p.1 ∈ M)
    (htr : ∀ p ∈ Gr, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ)
    (hdense : ∀ T ∈ M, ∀ ε > 0, ∃ p ∈ Gr, ‖(p.1 - T) τ.vec‖ < ε)
    (hsep : ∀ T ∈ M, T τ.vec = 0 → T = 0) :
    ∃ Φ : ↥M.toStarSubalgebra →⋆ₐ[ℂ] Ultrapower σ ω, Function.Injective Φ ∧
      (∀ T : ↥M.toStarSubalgebra, ultratrace σ ω (Φ T) = ⟪τ.vec, (T : H →L[ℂ] H) τ.vec⟫_ℂ) ∧
      ∀ p ∈ Gr, ∀ h : p.1 ∈ M, Φ ⟨p.1, h⟩ = p.2 := by
  have hmem : ∀ T : ↥M.toStarSubalgebra, (T : H →L[ℂ] H) ∈ M := fun T ↦ T.2
  choose f hf using fun T : ↥M.toStarSubalgebra ↦ exists_rel τ Gr hω hGM htr hdense (hmem T)
  have hfeq : ∀ T : ↥M.toStarSubalgebra, ∀ v, Rel τ Gr (T : H →L[ℂ] H) v → f T = v :=
    fun T v h ↦ rel_unique τ Gr htr (hf T) h
  let Φ : ↥M.toStarSubalgebra →⋆ₐ[ℂ] Ultrapower σ ω :=
    { toFun := f
      map_one' := hfeq 1 1 (rel_one τ Gr)
      map_mul' := fun T S ↦ hfeq (T * S) _ (rel_mul τ Gr hGM (hmem T) (hf T) (hf S))
      map_zero' := hfeq 0 0 (rel_zero τ Gr)
      map_add' := fun T S ↦ hfeq (T + S) _ (rel_add τ Gr (hf T) (hf S))
      commutes' := fun c ↦ hfeq (algebraMap ℂ _ c) _ (rel_algebraMap τ Gr c)
      map_star' := fun T ↦ hfeq (star T) _ (rel_star τ Gr hGM (hmem T) (hf T)) }
  refine ⟨Φ, (injective_iff_map_eq_zero Φ).mpr fun T hT ↦ ?_, fun T ↦ rel_trace τ Gr htr (hf T),
    fun p hp h ↦ hfeq ⟨p.1, h⟩ p.2 (rel_of_mem τ Gr hp)⟩
  have h2 : ⟪τ.vec, (star (T : H →L[ℂ] H) * T) τ.vec⟫_ℂ = 0 := by
    have h1 := rel_trace τ Gr htr (hf (star T * T))
    have h3 : f (star T * T) = 0 := by
      show Φ (star T * T) = 0
      rw [map_mul, map_star, hT, star_zero, zero_mul]
    rw [h3, map_zero] at h1
    exact h1.symm
  rw [τ.inner_star_mul_self, Complex.ofReal_eq_zero, pow_eq_zero_iff two_ne_zero,
    norm_eq_zero] at h2
  exact Subtype.ext (hsep (T : H →L[ℂ] H) (hmem T) h2)

end

end GroupApproximation.SimpleKazhdanSofic.ROmega

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.rel_mul
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.exists_rel_qfun
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.exists_extension
