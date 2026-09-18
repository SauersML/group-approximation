import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.GraphRel
import Mathlib.Tactic.Module
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's formulation: extending a trace-preserving `⋆`-homomorphism from a dense graph

`simple_kazhdan_sofic_group.tex`, subsection "Brown's formulation":
"`L(G)` embeds in `𝓡^ω`" and "`L(G) ⊗̄ 𝓡` ... embeds in `𝓡^ω`".

This is the fourth step of this lane's route to those embeddings. It continues
`Full/BrownROmega/GraphRel`. Let `M` be a von Neumann algebra with a separating tracial vector
`ξ`, and let `Gr ⊆ M × N^ω` be a trace-preserving graph whose first coordinates are `‖·ξ‖`-dense
in `M`.

* Every self-adjoint `S = q(g(S))` with `‖S‖ ≤ 1/2` is related to something. Approximate `g(S)`
  by self-adjoint `pₖ ∈ Gr` and pass to `q(pₖ)`, which is `2`-norm Cauchy with the uniform
  bound `1/2`. Take the diagonal limit (`exists_limit`), and approximate `q` by polynomials so
  the approximants stay inside `Gr` with bounds.
* Scaling and `T = Re T + i Im T` give `GraphRel T (Φ T)` for every `T ∈ M`. The map `Φ` is an
  injective trace-preserving `⋆`-homomorphism that extends the graph (`exists_extension`).
-/

namespace GroupApproximation.Full.SK06

open Filter TracialUltrapower
open scoped InnerProductSpace Topology

noncomputable section

universe v

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialVector M)
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {N : VonNeumannAlgebra K} {σ : TracialVector N} {ω : Ultrafilter ℕ}
variable (Gr : StarSubalgebra ℂ ((H →L[ℂ] H) × Ultrapower σ ω))

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
    (hS : IsSelfAdjoint S) : ∃ v, GraphRel τ Gr (cfc qfun S) v := by
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
    (hT : IsSelfAdjoint T) (hTn : ‖T‖ ≤ 1 / 2) : ∃ v, GraphRel τ Gr T v := by
  have h := exists_rel_qfun τ Gr hω hGM htr hdense (cfc_mem_of_mem hTM gfun) (cfc_predicate gfun T)
  rwa [cfc_qfun_cfc_gfun T hT hTn] at h

/-- **Every self-adjoint element of `M` is related to something** (by scaling). -/
theorem exists_rel_sa (hω : (ω : Filter ℕ) ≤ cofinite) (hGM : ∀ p ∈ Gr, p.1 ∈ M)
    (htr : ∀ p ∈ Gr, ultratrace σ ω p.2 = ⟪τ.vec, p.1 τ.vec⟫_ℂ)
    (hdense : ∀ T ∈ M, ∀ ε > 0, ∃ p ∈ Gr, ‖(p.1 - T) τ.vec‖ < ε) {X : H →L[ℂ] H} (hXM : X ∈ M)
    (hX : IsSelfAdjoint X) : ∃ v, GraphRel τ Gr X v := by
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
    (hTM : T ∈ M) : ∃ v, GraphRel τ Gr T v := by
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
  have hfeq : ∀ T : ↥M.toStarSubalgebra, ∀ v, GraphRel τ Gr (T : H →L[ℂ] H) v → f T = v :=
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

end GroupApproximation.Full.SK06

#audit_axioms GroupApproximation.Full.SK06.exists_rel_qfun
#audit_axioms GroupApproximation.Full.SK06.exists_extension
