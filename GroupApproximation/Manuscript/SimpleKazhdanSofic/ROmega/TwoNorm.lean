import GroupApproximation.Analysis.TracialUltrapowerTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# `L(G) ↪ R^ω` and `L(G) ⊗̄ R ↪ R^ω`: the `2`-norm on a tracial ultrapower

`simple_kazhdan_sofic_group.tex`:

> (l.82–84) In Brown's form, $G_X$ lies in the unitary group of the McDuff factor
> $L(G_X)\mathbin{\bar\otimes}\mathcal R$, which embeds in $\mathcal R^\omega$.
>
> (tex 345–348) It is LEF, so it is sofic and hyperlinear, and $L(G)$ embeds in $\mathcal R^\omega$.
>
> (tex 350–355) Then $G$ lies in the unitary group of the McDuff factor
> $L(G)\mathbin{\bar\otimes}\mathcal R$, which embeds in
> $\mathcal R^\omega\mathbin{\bar\otimes}\mathcal R\subseteq(\mathcal R\mathbin{\bar\otimes}
> \mathcal R)^\omega\cong\mathcal R^\omega$.

## Proof route of the lane (modules `ROmega/*`)

1. `TwoNorm` (this file): `‖x‖₂ = √(Re trω (x⋆x))` on `N^ω`, its triangle inequality, the bounds
   `‖a x‖₂ ≤ C ‖x‖₂`, faithfulness, and a *diagonal limit*: a family `d_k` of uniformly bounded
   sequences with `‖d_j − d_i‖₂ < δ_i` (`i ≤ j`) has a bounded limit `c` with `‖c − d_i‖₂ ≤ δ_i`.
   The limit is `c n = d_{κ(n)} n`, with `κ(n)` the largest `k ≤ n` for which all pairs `i ≤ j ≤ k`
   are `δ_i`-close at coordinate `n`.
2. `Resolvent`: for a self-adjoint operator `a`, `q(a) = a (1 + a²)⁻¹` via the continuous functional
   calculus.  It stays in a von Neumann algebra (bicommutant), `‖q(a)‖ ≤ 1/2`, it satisfies the
   algebraic identity `q(a) − q(b) = R_a (a − b) R_b − R_a a (a − b) b R_b`, hence
   `‖(q(a) − q(b)) ξ‖ ≤ 2 ‖(a − b) ξ‖` for a tracial vector `ξ`.  It inverts
   `g(t) = 2t/(1 + √(1 − 4t²))` on `‖T‖ ≤ 1/2`, and it is uniformly approximated on bounded
   spectra by polynomials.
3. `Extension`: a trace-preserving `⋆`-homomorphism on a `‖·ξ‖`-dense `⋆`-subalgebra of a von
   Neumann algebra `M` with separating tracial vector `ξ` extends to an injective trace-preserving
   `⋆`-homomorphism `M → N^ω`.  The extension is the closure of the graph with uniform bounds
   (Kaplansky density is replaced by `q` and step 1).
4. `TwistedModel`: for a sign cocycle `σ` on `Γ`, a map `W : Γ → N^ω` with `W 1 = 1`,
   `W g W h = (−1)^{σ(g,h)} W (gh)`, unitary values and `trω (W g) = 0` for `g ≠ 1` yields the graph
   algebra spanned by `(λ_σ(g), W g)`, so `L_σ(Γ)` embeds in `N^ω`.
5. `GroupModel`, `PauliShift`, `TensorModel`: sofic approximations and the matrix-to-hyperfinite
   map of the corpus give `v : G → R^ω`; Pauli operators on shifted coordinates give `w : P → R^ω`
   commuting with `v`, so `W (p, g) = w p · v g` realizes the product cocycle, and
   `L(G) ⊗̄ R = L_{σ×0}(P × G)`.
6. `MainSentence`: the endpoints.
-/

namespace GroupApproximation.SimpleKazhdanSofic.ROmega

open Filter TracialUltrapower
open scoped InnerProductSpace Topology

noncomputable section

universe v

variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {N : VonNeumannAlgebra K} (σ : TracialVector N) (ω : Ultrafilter ℕ)

/-- **The `2`-norm** `‖x‖₂ = √(Re trω (x⋆x))` on the tracial ultrapower. -/
def twoNorm (x : Ultrapower σ ω) : ℝ :=
  Real.sqrt (ultratrace σ ω (star x * x)).re

theorem twoNorm_nonneg (x : Ultrapower σ ω) : 0 ≤ twoNorm σ ω x :=
  Real.sqrt_nonneg _

/-- `‖aₙ ξ‖ → ‖[a]‖₂` along `ω`. -/
theorem tendsto_twoNorm_mk (a : boundedSeq N) :
    Tendsto (fun n ↦ ‖(a : ℕ → (K →L[ℂ] K)) n σ.vec‖) (ω : Filter ℕ)
      (𝓝 (twoNorm σ ω (mk σ ω a))) := by
  have h2 : Tendsto (fun n ↦ ‖(a : ℕ → (K →L[ℂ] K)) n σ.vec‖ ^ 2) (ω : Filter ℕ)
      (𝓝 (seqUltratrace σ ω (star a * a)).re) := by
    refine Tendsto.congr (fun n ↦ ?_)
      ((Complex.continuous_re.tendsto _).comp (tendsto_seqUltratrace σ ω (star a * a)))
    rw [Function.comp_apply, seqTrace_star_mul_self, Complex.ofReal_re]
  have e : twoNorm σ ω (mk σ ω a) = Real.sqrt (seqUltratrace σ ω (star a * a)).re := by
    rw [twoNorm, star_mk, ← map_mul (mk σ ω), ultratrace_mk]
  rw [e]
  refine Tendsto.congr (fun n ↦ ?_) h2.sqrt
  exact Real.sqrt_sq (norm_nonneg _)

theorem twoNorm_mk_le {a : boundedSeq N} {f : ℕ → ℝ} {L : ℝ} (hf : Tendsto f (ω : Filter ℕ) (𝓝 L))
    (h : ∀ n, ‖(a : ℕ → (K →L[ℂ] K)) n σ.vec‖ ≤ f n) : twoNorm σ ω (mk σ ω a) ≤ L :=
  le_of_tendsto_of_tendsto' (tendsto_twoNorm_mk σ ω a) hf h

theorem twoNorm_zero : twoNorm σ ω 0 = 0 := by
  rw [twoNorm, star_zero, zero_mul, map_zero, Complex.zero_re, Real.sqrt_zero]

theorem twoNorm_add_le (x y : Ultrapower σ ω) :
    twoNorm σ ω (x + y) ≤ twoNorm σ ω x + twoNorm σ ω y := by
  obtain ⟨a, rfl⟩ := mk_surjective σ ω x
  obtain ⟨b, rfl⟩ := mk_surjective σ ω y
  rw [← map_add (mk σ ω)]
  exact twoNorm_mk_le σ ω ((tendsto_twoNorm_mk σ ω a).add (tendsto_twoNorm_mk σ ω b))
    fun n ↦ norm_add_le ((a : ℕ → (K →L[ℂ] K)) n σ.vec) ((b : ℕ → (K →L[ℂ] K)) n σ.vec)

theorem twoNorm_sub_comm (x y : Ultrapower σ ω) : twoNorm σ ω (x - y) = twoNorm σ ω (y - x) := by
  obtain ⟨a, rfl⟩ := mk_surjective σ ω x
  obtain ⟨b, rfl⟩ := mk_surjective σ ω y
  rw [← map_sub (mk σ ω), ← map_sub (mk σ ω)]
  refine tendsto_nhds_unique (tendsto_twoNorm_mk σ ω (a - b)) ?_
  refine Tendsto.congr (fun n ↦ ?_) (tendsto_twoNorm_mk σ ω (b - a))
  exact norm_sub_rev ((b : ℕ → (K →L[ℂ] K)) n σ.vec) ((a : ℕ → (K →L[ℂ] K)) n σ.vec)

theorem twoNorm_sub_le (x y z : Ultrapower σ ω) :
    twoNorm σ ω (x - z) ≤ twoNorm σ ω (x - y) + twoNorm σ ω (y - z) := by
  calc twoNorm σ ω (x - z) = twoNorm σ ω ((x - y) + (y - z)) := by rw [sub_add_sub_cancel]
    _ ≤ twoNorm σ ω (x - y) + twoNorm σ ω (y - z) := twoNorm_add_le σ ω _ _

theorem twoNorm_star (x : Ultrapower σ ω) : twoNorm σ ω (star x) = twoNorm σ ω x := by
  obtain ⟨a, rfl⟩ := mk_surjective σ ω x
  rw [star_mk]
  refine tendsto_nhds_unique (tendsto_twoNorm_mk σ ω (star a)) ?_
  exact Tendsto.congr (fun n ↦ (σ.norm_star_apply (coord_mem a n)).symm) (tendsto_twoNorm_mk σ ω a)

theorem twoNorm_smul (c : ℂ) (x : Ultrapower σ ω) :
    twoNorm σ ω (c • x) = ‖c‖ * twoNorm σ ω x := by
  obtain ⟨a, rfl⟩ := mk_surjective σ ω x
  rw [← mk_smul]
  refine tendsto_nhds_unique (tendsto_twoNorm_mk σ ω (c • a)) ?_
  refine Tendsto.congr (fun n ↦ ?_) ((tendsto_twoNorm_mk σ ω a).const_mul ‖c‖)
  show ‖c‖ * ‖(a : ℕ → (K →L[ℂ] K)) n σ.vec‖ = ‖(c • (a : ℕ → (K →L[ℂ] K)) n) σ.vec‖
  rw [_root_.smul_apply, norm_smul]

theorem eq_zero_of_twoNorm_eq_zero {x : Ultrapower σ ω} (h : twoNorm σ ω x = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := mk_surjective σ ω x
  rw [mk_eq_zero_iff]
  have ht := tendsto_twoNorm_mk σ ω a
  rw [h] at ht
  exact ht

theorem eq_of_twoNorm_sub_le {x y : Ultrapower σ ω} (h : ∀ ε > 0, twoNorm σ ω (x - y) ≤ ε) :
    x = y := by
  refine sub_eq_zero.mp (eq_zero_of_twoNorm_eq_zero σ ω ?_)
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) (twoNorm_nonneg σ ω _)
  rw [zero_add]
  exact h ε hε

theorem norm_ultratrace_le_twoNorm (x : Ultrapower σ ω) : ‖ultratrace σ ω x‖ ≤ twoNorm σ ω x := by
  obtain ⟨a, rfl⟩ := mk_surjective σ ω x
  rw [ultratrace_mk]
  exact le_of_tendsto_of_tendsto' (tendsto_seqUltratrace σ ω a).norm (tendsto_twoNorm_mk σ ω a)
    fun n ↦ σ.norm_inner_apply_le_norm_apply ((a : ℕ → (K →L[ℂ] K)) n)

/-- `‖a x‖₂ ≤ C ‖x‖₂` for a sequence `a` bounded by `C`. -/
theorem twoNorm_mk_mul_le {a : boundedSeq N} {C : ℝ} (hC : ∀ n, ‖(a : ℕ → (K →L[ℂ] K)) n‖ ≤ C)
    (y : Ultrapower σ ω) : twoNorm σ ω (mk σ ω a * y) ≤ C * twoNorm σ ω y := by
  obtain ⟨b, rfl⟩ := mk_surjective σ ω y
  rw [← map_mul (mk σ ω)]
  refine twoNorm_mk_le σ ω ((tendsto_twoNorm_mk σ ω b).const_mul C) fun n ↦ ?_
  calc ‖((a * b : boundedSeq N) : ℕ → (K →L[ℂ] K)) n σ.vec‖
      = ‖(a : ℕ → (K →L[ℂ] K)) n ((b : ℕ → (K →L[ℂ] K)) n σ.vec)‖ := rfl
    _ ≤ ‖(a : ℕ → (K →L[ℂ] K)) n‖ * ‖(b : ℕ → (K →L[ℂ] K)) n σ.vec‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖(b : ℕ → (K →L[ℂ] K)) n σ.vec‖ := mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)

/-- `‖x b‖₂ ≤ C ‖x‖₂` for a sequence `b` bounded by `C` (traciality). -/
theorem twoNorm_mul_mk_le {b : boundedSeq N} {C : ℝ} (hC : ∀ n, ‖(b : ℕ → (K →L[ℂ] K)) n‖ ≤ C)
    (x : Ultrapower σ ω) : twoNorm σ ω (x * mk σ ω b) ≤ C * twoNorm σ ω x := by
  obtain ⟨a, rfl⟩ := mk_surjective σ ω x
  rw [← map_mul (mk σ ω)]
  refine twoNorm_mk_le σ ω ((tendsto_twoNorm_mk σ ω a).const_mul C) fun n ↦ ?_
  calc ‖((a * b : boundedSeq N) : ℕ → (K →L[ℂ] K)) n σ.vec‖
      = ‖((a : ℕ → (K →L[ℂ] K)) n * (b : ℕ → (K →L[ℂ] K)) n) σ.vec‖ := rfl
    _ ≤ ‖(b : ℕ → (K →L[ℂ] K)) n‖ * ‖(a : ℕ → (K →L[ℂ] K)) n σ.vec‖ :=
      σ.norm_mul_apply_le (coord_mem a n) (coord_mem b n)
    _ ≤ C * ‖(a : ℕ → (K →L[ℂ] K)) n σ.vec‖ := mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)

/-- Pointwise operator-norm closeness gives `2`-norm closeness. -/
theorem twoNorm_mk_sub_le {a b : boundedSeq N} {η : ℝ}
    (h : ∀ n, ‖(a : ℕ → (K →L[ℂ] K)) n - (b : ℕ → (K →L[ℂ] K)) n‖ ≤ η) :
    twoNorm σ ω (mk σ ω a - mk σ ω b) ≤ η := by
  rw [← map_sub (mk σ ω)]
  refine twoNorm_mk_le σ ω tendsto_const_nhds fun n ↦ ?_
  calc ‖((a - b : boundedSeq N) : ℕ → (K →L[ℂ] K)) n σ.vec‖
      = ‖((a : ℕ → (K →L[ℂ] K)) n - (b : ℕ → (K →L[ℂ] K)) n) σ.vec‖ := rfl
    _ ≤ ‖(a : ℕ → (K →L[ℂ] K)) n - (b : ℕ → (K →L[ℂ] K)) n‖ := σ.norm_apply_le _
    _ ≤ η := h n

/-- Pairs `i ≤ j ≤ i₀` are eventually close at the coordinates. -/
theorem eventually_pairs_close (d : ℕ → boundedSeq N) (δ : ℕ → ℝ)
    (hd : ∀ i j, i ≤ j → twoNorm σ ω (mk σ ω (d j) - mk σ ω (d i)) < δ i) (i₀ : ℕ) :
    ∀ᶠ n in (ω : Filter ℕ), ∀ p : Fin (i₀ + 1) × Fin (i₀ + 1), (p.1 : ℕ) ≤ p.2 →
      ‖((d p.2 : ℕ → (K →L[ℂ] K)) n - (d p.1 : ℕ → (K →L[ℂ] K)) n) σ.vec‖ < δ p.1 := by
  refine Filter.eventually_all.mpr fun p ↦ ?_
  by_cases hp : (p.1 : ℕ) ≤ p.2
  · have ht := tendsto_twoNorm_mk σ ω (d p.2 - d p.1)
    rw [map_sub] at ht
    filter_upwards [ht.eventually (gt_mem_nhds (hd p.1 p.2 hp))] with n hn
    exact fun _ ↦ hn
  · exact Filter.Eventually.of_forall fun _ h ↦ absurd h hp

/-- **Diagonal limit.** A uniformly bounded family `d_k` with `‖d_j − d_i‖₂ < δ_i` for `i ≤ j` has a
limit `c`, bounded by the same bound, with `‖c − d_i‖₂ ≤ δ_i`. -/
theorem exists_limit (hω : (ω : Filter ℕ) ≤ cofinite) (d : ℕ → boundedSeq N) {B : ℝ}
    (hB : ∀ k n, ‖(d k : ℕ → (K →L[ℂ] K)) n‖ ≤ B) (δ : ℕ → ℝ)
    (hd : ∀ i j, i ≤ j → twoNorm σ ω (mk σ ω (d j) - mk σ ω (d i)) < δ i) :
    ∃ c : boundedSeq N, (∀ n, ‖(c : ℕ → (K →L[ℂ] K)) n‖ ≤ B) ∧
      ∀ i, twoNorm σ ω (mk σ ω c - mk σ ω (d i)) ≤ δ i := by
  classical
  let P : ℕ → ℕ → Prop := fun n k ↦ ∀ i j, i ≤ j → j ≤ k →
      ‖((d j : ℕ → (K →L[ℂ] K)) n - (d i : ℕ → (K →L[ℂ] K)) n) σ.vec‖ < δ i
  let κ : ℕ → ℕ := fun n ↦ Nat.findGreatest (P n) n
  have hc : (fun n ↦ (d (κ n) : ℕ → (K →L[ℂ] K)) n) ∈ boundedSeq N :=
    mem_boundedSeq_iff.mpr ⟨fun n ↦ coord_mem (d (κ n)) n, B, fun n ↦ hB (κ n) n⟩
  refine ⟨⟨_, hc⟩, fun n ↦ hB (κ n) n, fun i ↦ ?_⟩
  have ht := tendsto_twoNorm_mk σ ω ((⟨_, hc⟩ : boundedSeq N) - d i)
  rw [map_sub] at ht
  refine le_of_tendsto ht ?_
  have hcof : ∀ᶠ n in (ω : Filter ℕ), i ≤ n :=
    hω (by rw [Nat.cofinite_eq_atTop]; exact Filter.eventually_ge_atTop i)
  filter_upwards [eventually_pairs_close σ ω d δ hd i, hcof] with n hn hin
  have hPi : P n i := fun i' j' hij hji ↦ hn (⟨i', by omega⟩, ⟨j', by omega⟩) hij
  have hle : i ≤ κ n := Nat.le_findGreatest hin hPi
  have hspec : P n (κ n) := Nat.findGreatest_spec hin hPi
  exact (hspec i (κ n) hle le_rfl).le

end

end GroupApproximation.SimpleKazhdanSofic.ROmega

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.exists_limit
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.twoNorm_mul_mk_le
