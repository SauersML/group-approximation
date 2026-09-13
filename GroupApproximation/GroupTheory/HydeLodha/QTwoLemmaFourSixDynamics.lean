import GroupApproximation.GroupTheory.HydeLodha.QTwoLemmaFourSixStatements
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationGermGamma
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationStabKSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Hyde–Lodha Lemma 4.6: the dynamics

Hyde–Lodha, Lemma 4.6 (tex 867–869, `\label{FPlem3}`): "For all `Γ` satisfying `Q_n ≤ Γ ≤ Γ_n` and
`I = [a, b] ⊂ ℝ` with `|I| ≤ 1`, `Υ_Γ(I)` is of type `F_∞`."  This module proves the dynamical input
of its proof, `LemmaFourSixDynamicsStatement` (`QTwoLemmaFourSixStatements`), for `Q₂ ≤ Γ₂` in the
unit frame `0 < a < b < 1` with grid endpoints.

* tex 874: "Using Lemma \ref{FPlem1}, we find `f ∈ Υ_{Q_n}(I)` such that `a·f_+', b·f_-' > 1`."
* tex 877–878: "Moreover, there exists a closed interval `J ⊂ (0,1) ∩ (a,b)` with endpoints in
  `ℤ[1/η_n]` so that `J·f ⊂ J` and `⋃_{n ∈ ℕ} J·f^{-n} = (a,b)`."
* tex 888–889: "Let `J_0 = J·f`. We choose `s_i ∈ Υ_{F_{η_n}'}(J) ≤ Υ_Γ(I)` such that
  `{J_i = J_0·s_i | 1 ≤ i ≤ η_n}` are pairwise disjoint intervals in `J \ J_0`."

`f ∈ Υ_{Q₂}(I)` has the germs `t ↦ a + 6 (t - a)` at `a⁺` and `t ↦ b + 6 (t - b)` at `b⁻`
(`exists_upsilon_qTwo_germs`).  For `λ = 6^{-L}` small, `J = [a + λ, b - λ]` and `J·f ⊆ [c, d]` with
`[c, d] = [a + 2λ, b - 2λ]`.  The covering property is the form Case 1 consumes: a power of `f` pushes
the support of any `k ∈ Υ^c_{Γ₂}(I)` into `(c + λ, d - λ)`.  The `s_i` are the powers `t^{i+1}` of one
commutator `t ∈ Υ_{Q₂}(J)` of moves with `t d ≤ c`, so the intervals `[c, d]·t^j` are pairwise
disjoint.

Permutations compose right to left: the paper's `J·f` is `f '' J`.
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement
open HigmanThompson

/-! ## Iterating the germ at `b⁻` -/

/-- The mirror of `germLeft_iterate_ge`: under the germ `t ↦ b + 6 (t - b)` at `b⁻`, the `n`-th
iterate moves `b - s` to the left of `b - min (6^n s) λ`. -/
theorem germRight_iterate_le {b ε lam : ℚ} {f : Equiv.Perm ℚ} (hf : GermRight 4 b 1 ε f)
    (hmono : StrictMono f) (hlam0 : 0 ≤ lam) (hlam : lam ≤ ε) {s : ℚ} (hs : 0 ≤ s) (n : ℕ) :
    (f ^ n) (b - s) ≤ b - min ((6 : ℚ) ^ n * s) lam := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, Equiv.Perm.one_apply]
    linarith [min_le_left s lam]
  | succ n ih =>
    rw [pow_succ' f n, Equiv.Perm.mul_apply]
    have hm0 : 0 ≤ min ((6 : ℚ) ^ n * s) lam := le_min (by positivity) hlam0
    have hm1 : min ((6 : ℚ) ^ n * s) lam ≤ lam := min_le_right _ _
    have h1 := hmono.monotone ih
    have h2 : f (b - min ((6 : ℚ) ^ n * s) lam) = b - 6 * min ((6 : ℚ) ^ n * s) lam := by
      rw [hf.2 _ (by linarith) (by linarith), zpow_one, six_cast]
      ring
    rw [h2] at h1
    have h3 : min ((6 : ℚ) ^ (n + 1) * s) lam ≤ 6 * min ((6 : ℚ) ^ n * s) lam := by
      rcases min_cases ((6 : ℚ) ^ n * s) lam with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
        exact (min_le_left _ _).trans (le_of_eq (by ring))
      · rw [h]
        exact (min_le_right _ _).trans (by linarith)
    linarith

/-! ## Disjoint periodic intervals -/

theorem disjoint_perIoo_of_le {p q p' q' : ℚ} (hqp : q ≤ p') (hq' : q' ≤ p + 1) :
    Disjoint (perIoo p q) (perIoo p' q') :=
  (disjoint_perIoo (c := p) (d := q) (e := p + 1) le_rfl).mono_right (perIoo_mono hqp hq')

/-! ## Moves inside `Υ_{Γ₂}` -/

/-- A move of `Rstab_{F_6}([p, q])` (`exists_move`), made periodic: for grid points `0 < p < q < 1`
and `x`, `y` in `(p, q)` with the same residue, some element of `Υ_{Γ₂}([p, q])` sends `x` to `y`. -/
theorem exists_upsilon_gammaTwo_move {p q x y : ℚ} (hp : ∃ M, p ∈ Grid 6 M)
    (hq : ∃ M, q ∈ Grid 6 M) (hres : ResEq 4 x y) (h0p : 0 < p) (hpx : p < x) (hpy : p < y)
    (hxq : x < q) (hyq : y < q) (hq1 : q < 1) : ∃ K ∈ upsilon gammaTwo p q, K x = y := by
  obtain ⟨h, hP, hlo, hhi, hxy⟩ := exists_move 4 hp hq hres hpx hpy hxq hyq
  have hr : h ∈ rstab 4 p q := ⟨hP, hlo, hhi⟩
  have hc : h ∈ compactF 4 1 := rstab_le_compactF_one (m := 4) h0p.le hq1.le hr
  refine ⟨perHom 4 ⟨h, hc⟩, ?_, ?_⟩
  · rw [upsilon_gammaTwo_eq_map h0p (hpx.trans hxq) hq1]
    exact Subgroup.mem_map.mpr ⟨⟨h, hc⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  · rw [perHom_apply_of_mem 4 _ (by linarith) (by linarith)]
    exact hxy

/-- One element `t ∈ Υ_{Q₂}([e₁, e₂])` pushing `d` below `c`: the commutator of a move `K` taking
`β ∈ (d, e₂)` below `α ∈ (e₁, c)` and a move `H` supported in `(α, β)` taking `d` below `c`. -/
theorem exists_upsilon_qTwo_push {e₁ e₂ c d : ℚ} (he₁ : ∃ M, e₁ ∈ Grid 6 M)
    (he₂ : ∃ M, e₂ ∈ Grid 6 M) (hd : ∃ M, d ∈ Grid 6 M) (h0 : 0 < e₁) (h1 : e₁ < c) (h2 : c < d)
    (h3 : d < e₂) (h4 : e₂ < 1) : ∃ t ∈ upsilon qTwo e₁ e₂, t d ≤ c := by
  obtain ⟨α, hα1, hα2, hα⟩ := exists_grid_mem_Ioo (m := 4) h1
  obtain ⟨β, hβ1, hβ2, hβ⟩ := exists_grid_mem_Ioo (m := 4) h3
  obtain ⟨z, hz1, hz2, hzβ, -⟩ := exists_resEq_mem_Ioo (m := 4) hβ hα1
  obtain ⟨y, hy1, hy2, hyd, -⟩ := exists_resEq_mem_Ioo (m := 4) hd hα2
  obtain ⟨K, hK, hKβ⟩ := exists_upsilon_gammaTwo_move he₁ he₂ hzβ.symm h0 (by linarith) hz1
    hβ2 (by linarith) h4
  obtain ⟨H, hH, hHd⟩ := exists_upsilon_gammaTwo_move hα hβ hyd.symm (by linarith)
    (by linarith) hy1 hβ1 (by linarith) (by linarith)
  have hKΓ : K ∈ gammaTwo := (mem_upsilon.mp hK).1
  have hHΓ : H ∈ gammaTwo := (mem_upsilon.mp hH).1
  have hH' : H ∈ upsilon gammaTwo e₁ e₂ := upsilon_mono le_rfl (perIoo_mono hα1.le hβ2.le) hH
  have hHK : ⁅H, K⁆ ∈ upsilon gammaTwo e₁ e₂ := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hH' hK) (inv_mem hH')) (inv_mem hK)
  refine ⟨⁅H, K⁆, mem_upsilon.mpr ⟨Subgroup.commutator_mem_commutator hHΓ hKΓ,
    (mem_upsilon.mp hHK).2⟩, ?_⟩
  have hKmono := gammaTwo_strictMono hKΓ
  have hKe₂ : K e₂ = e₂ :=
    (mem_upsilon.mp hK).2 e₂ (not_mem_perIoo_of_unit h0 h4 (by linarith) h4 (Or.inr le_rfl))
  have hKw : K (K⁻¹ d) = d := Equiv.Perm.eq_inv_iff_eq.mp rfl
  have hβw : β ≤ K⁻¹ d := not_lt.mp fun hlt => by
    have h := hKmono hlt
    rw [hKw, hKβ] at h
    linarith
  have hwe₂ : K⁻¹ d ≤ e₂ := not_lt.mp fun hlt => by
    have h := hKmono hlt
    rw [hKw, hKe₂] at h
    linarith
  have hHw : H (K⁻¹ d) = K⁻¹ d :=
    (mem_upsilon.mp hH).2 (K⁻¹ d) (not_mem_perIoo_of_unit (by linarith) (by linarith)
      (by linarith) (by linarith) (Or.inr hβw))
  have hHinv : H⁻¹ (K⁻¹ d) = K⁻¹ d := Equiv.Perm.inv_eq_iff_eq.mpr hHw.symm
  rw [commutatorElement_def]
  simp only [Equiv.Perm.mul_apply]
  rw [hHinv, hKw, hHd]
  exact hy2.le

/-- The intervals `[c, d]·t^j` are pairwise disjoint when `t ∈ Υ_{Q₂}([e₁, e₂])` pushes `d` below
`c`. -/
theorem disjoint_pow_image {t : Equiv.Perm ℚ} {e₁ e₂ c d : ℚ} (ht : t ∈ upsilon qTwo e₁ e₂)
    (h0 : 0 < e₁) (hc : e₁ < c) (hcd : c < d) (hd : d < e₂) (h1 : e₂ < 1) (htd : t d ≤ c)
    {i j : ℕ} (hij : i < j) : Disjoint ((t ^ j) '' perIoo c d) ((t ^ i) '' perIoo c d) := by
  have hmem : ∀ n : ℕ, t ^ n ∈ upsilon qTwo e₁ e₂ := fun n => (upsilon qTwo e₁ e₂).pow_mem ht n
  have hΓ : ∀ n : ℕ, t ^ n ∈ gammaTwo := fun n => qTwo_le_gammaTwo (mem_upsilon.mp (hmem n)).1
  have hmono : ∀ n : ℕ, StrictMono (t ^ n) := fun n => gammaTwo_strictMono (hΓ n)
  have hfix₁ : ∀ n : ℕ, (t ^ n) e₁ = e₁ := fun n =>
    (mem_upsilon.mp (hmem n)).2 e₁ (not_mem_perIoo_of_unit h0 h1 h0.le (by linarith) (Or.inl le_rfl))
  have hfix₂ : ∀ n : ℕ, (t ^ n) e₂ = e₂ := fun n =>
    (mem_upsilon.mp (hmem n)).2 e₂ (not_mem_perIoo_of_unit h0 h1 (by linarith) h1 (Or.inr le_rfl))
  have hstep : ∀ n : ℕ, (t ^ (n + 1)) d ≤ (t ^ n) c := fun n => by
    rw [pow_succ, Equiv.Perm.mul_apply]
    exact (hmono n).monotone htd
  have hanti : Antitone fun n : ℕ => (t ^ n) d :=
    antitone_nat_of_succ_le fun n => (hstep n).trans ((hmono n).monotone hcd.le)
  refine Set.disjoint_of_subset (image_perIoo_subset (hΓ j) c d) (image_perIoo_subset (hΓ i) c d)
    (disjoint_perIoo_of_le ((hanti (show i + 1 ≤ j by omega)).trans (hstep i)) ?_)
  have hi := (hmono i).monotone hd.le
  have hj := (hmono j).monotone hc.le
  rw [hfix₂ i] at hi
  rw [hfix₁ j] at hj
  linarith

/-! ## The endpoint -/

/-- **Hyde–Lodha Lemma 4.6, the dynamics** (tex 874, 877–878 and 888–889, in the proof of
`\label{FPlem3}`), for `Q₂ ≤ Γ₂` in the unit frame with grid endpoints. -/
theorem lemmaFourSixDynamics : LemmaFourSixDynamicsStatement := by
  intro a b ha hb h0a hab hb1
  obtain ⟨f, hf, ε, hgl, hgr⟩ := exists_upsilon_qTwo_germs ha hb h0a hab hb1
  have hfΓ : f ∈ gammaTwo := qTwo_le_gammaTwo (mem_upsilon.mp hf).1
  have hmono : StrictMono f := gammaTwo_strictMono hfΓ
  obtain ⟨Ma, hMa⟩ := ha
  obtain ⟨Mb, hMb⟩ := hb
  obtain ⟨L, hL, hlam⟩ :=
    exists_level (m := 4) (max Ma Mb) (δ := min ε ((b - a) / 20)) (lt_min hgl.1 (by linarith))
  have hlamg := mTwoPow_inv_mem_grid (m := 4) L
  have hlam0 := sixInv_pos L
  generalize ((((4 : ℕ) : ℚ) + 2) ^ L)⁻¹ = lam at hlam hlamg hlam0
  have hlε : lam ≤ ε := hlam.trans (min_le_left _ _)
  have hlab : lam ≤ (b - a) / 20 := hlam.trans (min_le_right _ _)
  have haL : a ∈ Grid 6 L := grid_mono (le_trans (le_max_left _ _) hL) hMa
  have hbL : b ∈ Grid 6 L := grid_mono (le_trans (le_max_right _ _) hL) hMb
  have he₁ : a + lam ∈ Grid 6 L := grid_add haL hlamg
  have he₂ : b - lam ∈ Grid 6 L := grid_sub hbL hlamg
  have hc : a + lam + lam ∈ Grid 6 L := grid_add he₁ hlamg
  have hd : b - lam - lam ∈ Grid 6 L := grid_sub he₂ hlamg
  obtain ⟨t, ht, htd⟩ := exists_upsilon_qTwo_push (e₁ := a + lam) (e₂ := b - lam)
    (c := a + lam + lam) (d := b - lam - lam) ⟨L, he₁⟩ ⟨L, he₂⟩ ⟨L, hd⟩
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨f, hf, ⟨ε, hgl⟩, a + lam, b - lam, a + lam + lam, b - lam - lam, ⟨L, hc⟩, ⟨L, hd⟩,
    by linarith, by linarith, by linarith, by linarith, by linarith, ?_, ?_, ?_,
    fun i => t ^ (i.val + 1), fun i => (upsilon qTwo _ _).pow_mem ht _, ?_, ?_⟩
  · rw [hgl.2 (a + lam) (by linarith) (by linarith), zpow_one, six_cast]
    linarith
  · rw [hgr.2 (b - lam) (by linarith) (by linarith), zpow_one, six_cast]
    linarith
  · intro k hk
    obtain ⟨hkΓ, δ, hδ, hks⟩ := mem_upsilonc.mp hk
    have hδ' : 0 < min δ lam := lt_min hδ hlam0
    obtain ⟨N, -, hN⟩ := exists_level (m := 4) 0 hδ'
    rw [six_cast] at hN
    have h6 : (0 : ℚ) < 6 ^ N := by positivity
    have hbig := mul_le_mul_of_nonneg_left hN h6.le
    rw [mul_inv_cancel₀ h6.ne'] at hbig
    have hmin : min ((6 : ℚ) ^ N * min δ lam) lam = lam := min_eq_right (by linarith)
    have hks' : SupportedIn k (perIoo (a + min δ lam) (b - min δ lam)) :=
      hks.mono (perIoo_mono (by linarith [min_le_left δ lam]) (by linarith [min_le_left δ lam]))
    have hk' : k ∈ upsilon gammaTwo (a + min δ lam) (b - min δ lam) := mem_upsilon.mpr ⟨hkΓ, hks'⟩
    have hfn : f ^ (N + 1) ∈ gammaTwo := gammaTwo.pow_mem hfΓ _
    have hconj := conj_mem_upsilon hfn (fun x hx => gammaTwo_normalized x hx _ hfn) hk'
    have hlo := germLeft_iterate_ge hgl hmono hlam0.le hlε hδ'.le N
    have hhi := germRight_iterate_le hgr hmono hlam0.le hlε hδ'.le N
    rw [hmin] at hlo hhi
    have hlo' : a + lam + lam + lam ≤ (f ^ (N + 1)) (a + min δ lam) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
      have h := hmono.monotone hlo
      rw [hgl.2 (a + lam) (by linarith) (by linarith), zpow_one, six_cast] at h
      linarith
    have hhi' : (f ^ (N + 1)) (b - min δ lam) ≤ b - lam - lam - lam := by
      rw [pow_succ', Equiv.Perm.mul_apply]
      have h := hmono.monotone hhi
      rw [hgr.2 (b - lam) (by linarith) (by linarith), zpow_one, six_cast] at h
      linarith
    obtain ⟨hΓ', hsupp⟩ := mem_upsilon.mp (upsilon_mono le_rfl (perIoo_mono hlo' hhi') hconj)
    exact ⟨N + 1, mem_upsilonc.mpr ⟨hΓ', lam, hlam0, hsupp⟩⟩
  · intro i
    have h := disjoint_pow_image ht (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) htd (show 0 < i.val + 1 by omega)
    rwa [pow_zero, Equiv.Perm.coe_one, Set.image_id] at h
  · intro i j hij
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases Nat.lt_or_ge i.val j.val with h | h
    · exact (disjoint_pow_image ht (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) htd (show i.val + 1 < j.val + 1 by omega)).symm
    · exact disjoint_pow_image ht (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) htd (show j.val + 1 < i.val + 1 by omega)

#audit_axioms GroupApproximation.HydeLodha.germRight_iterate_le
#audit_axioms GroupApproximation.HydeLodha.disjoint_perIoo_of_le
#audit_axioms GroupApproximation.HydeLodha.exists_upsilon_gammaTwo_move
#audit_axioms GroupApproximation.HydeLodha.exists_upsilon_qTwo_push
#audit_axioms GroupApproximation.HydeLodha.disjoint_pow_image
#audit_closed_axioms GroupApproximation.HydeLodha.lemmaFourSixDynamics

end HydeLodha
end GroupApproximation
