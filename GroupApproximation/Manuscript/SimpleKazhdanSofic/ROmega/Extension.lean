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

* `Rel T v`: `(T, v)` is approximated by elements `p ∈ Gr` with `‖p₁‖` and a representative of `p₂`
  uniformly bounded, `‖(p₁ − T) ξ‖` and `‖p₂ − v‖₂` small.  Traciality gives `‖p₂‖₂ = ‖p₁ ξ‖` on `Gr`,
  so `Rel` is a function, and it is closed under `+`, `⋆`, scalars, and products (with `T ∈ M`).
* Every self-adjoint `S = q(g(S))`, `‖S‖ ≤ 1/2`, is related to something: approximate `g(S)` by
  self-adjoint `pₖ ∈ Gr`, pass to `q(pₖ)`, which is `2`-norm Cauchy with uniform bound `1/2`, take the
  diagonal limit (`exists_limit`), and approximate `q` by polynomials to stay inside `Gr` with bounds.
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
  push_neg at hcon
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

-- PART B

end

end GroupApproximation.SimpleKazhdanSofic.ROmega
