import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarNormKer
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarInjConj
import GroupApproximation.Meta.AxiomGuard

/-!
# `snd (ker fst) = ker ev₀` in `St(M, L[X])` (`M ≥ 3`)

Lane `bh-met-92f`.  Notation: `P = A ×_L L[X]`, `L = A_s`, `K = ker (fst : St(M, P) → St(M, A))`,
`S = snd (K)` (`k2KarInj_sndKer`), `kerB = ker (ev₀ : St(M, L[X]) → St(M, L))`
(`k2Karoubi_kerB`).

* `k2KarNorm_z_mem_sndKer`: `z_ij(h, r) = x_ji(r) x_ij(h) x_ji(r)⁻¹ ∈ S` for `h(0) = 0` and
  **any** `r ∈ L[X]`.  Write `x_ji(r) = snd (x_ji (lift r)) · x_ji(C (r(0)))` and use
  `k2KarInj_snd_conj_opp3` together with `snd`-conjugation invariance of `S`.
* `k2KarNorm_H_le_sndKer`: `H(X L[X]) ≤ S`.
* `k2KarNorm_sndKer_eq_kerB` (`M ≥ 3`): **`S = kerB`** (`≤` is `ev₀ ∘ snd = λ ∘ fst`, and `≥` is
  `kerB ≤ H(X L[X])` from `ElemFPK2KarNormKer`).
* Consequences: `S` is normal (`k2KarNorm_sndKer_normal`).  It is stable under conjugation by
  every `x_kl(C t)` and every `x_kl(g)` with `g(0) = 0`.  It contains
  `normalClosure {x_ij(h) : h(0) = 0}`, and `k2Karoubi_q : K → kerB` is **surjective**
  (`k2KarNorm_q_surjective`).

**Residual (LOUD: EQUIVALENT, not weaker).**  `ker q = {y : fst y = 1, snd y = 1}`, so `R1`
(`k2Karoubi_InjAt s`) says exactly that `ker q` consists of elements that die after padding.
With `q` surjective this is equivalent to `R1`, so no new `Statement` is introduced.  The
open target is still `k2Karoubi_InjAt s`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section KarNormSnd

variable {A : Type*} [CommRing A] {s : A} {M : ℕ}

/-- `S` is stable under conjugation by `snd y`, for any `y ∈ St(M, P)`. -/
theorem k2KarNorm_sndKer_conj (y : SteinbergGroup (Fin M) (k2DilateSt_pullback s))
    {z : SteinbergGroup (Fin M) (Polynomial (Localization.Away s))}
    (hz : z ∈ k2KarInj_sndKer s M) :
    ringMap (k2PullRel_snd s) y * z * (ringMap (k2PullRel_snd s) y)⁻¹ ∈ k2KarInj_sndKer s M := by
  obtain ⟨κ, hκ, rfl⟩ := k2KarInj_mem_sndKer.mp hz
  refine k2KarInj_mem_sndKer.mpr ⟨y * κ * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  rw [k2PullRel_mem_ker] at hκ ⊢
  rw [map_mul, map_mul, map_inv, hκ, mul_one, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_sndKer_conj

/-- `z_ij(h, r) ∈ S` for `h(0) = 0` and arbitrary `r ∈ L[X]` (`M ≥ 3`). -/
theorem k2KarNorm_z_mem_sndKer (hM : 3 ≤ M) (i j : Fin M) (hij : i ≠ j)
    {h : Polynomial (Localization.Away s)} (h0 : h.eval 0 = 0)
    (r : Polynomial (Localization.Away s)) :
    k2KarNorm_z i j hij h r ∈ k2KarInj_sndKer s M := by
  have hr : x j i hij.symm r = ringMap (k2PullRel_snd s) (x j i hij.symm (k2PullRel_lift s r)) *
      x j i hij.symm (Polynomial.C (r.eval 0)) := by
    rw [ringMap_x, k2PullRel_snd_lift, x_mul, sub_add_cancel]
  rw [k2KarNorm_z, hr, k2KarNorm_conj_conj]
  exact k2KarNorm_sndKer_conj _ (k2KarInj_snd_conj_opp3 hM i j hij (r.eval 0) h0)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_z_mem_sndKer

/-- `H(X L[X]) ≤ S` (`M ≥ 3`). -/
theorem k2KarNorm_H_le_sndKer (hM : 3 ≤ M) :
    k2KarNorm_H (Fin M) (RingHom.ker (Polynomial.evalRingHom (0 : Localization.Away s))) ≤
      k2KarInj_sndKer s M := by
  rw [k2KarNorm_H, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, h, hh, r, rfl⟩
  rw [RingHom.mem_ker, Polynomial.coe_evalRingHom] at hh
  exact k2KarNorm_z_mem_sndKer hM i j hij hh r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_H_le_sndKer

/-- **`snd (ker fst) = ker ev₀`** in `St(M, L[X])` (`M ≥ 3`). -/
theorem k2KarNorm_sndKer_eq_kerB (hM : 3 ≤ M) : k2KarInj_sndKer s M = k2Karoubi_kerB s M := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := k2KarInj_mem_sndKer.mp hz
    exact k2Karoubi_snd_mem hy
  · exact (k2KarNorm_ker_le_H (ι := Fin M) (R := Localization.Away s)
      (k2KarInj_exists_third hM)).trans (k2KarNorm_H_le_sndKer hM)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_sndKer_eq_kerB

/-- `ker ev₀ ⊆ S` (`M ≥ 3`). -/
theorem k2KarNorm_kerB_le_sndKer (hM : 3 ≤ M) : k2Karoubi_kerB s M ≤ k2KarInj_sndKer s M :=
  (k2KarNorm_sndKer_eq_kerB hM).ge

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_kerB_le_sndKer

/-- `S` is normal in `St(M, L[X])` (`M ≥ 3`). -/
theorem k2KarNorm_sndKer_normal (hM : 3 ≤ M) : (k2KarInj_sndKer s M).Normal := by
  rw [k2KarNorm_sndKer_eq_kerB hM]
  infer_instance

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_sndKer_normal

/-- `S` is normalized by every constant root `x_kl(C t)` (`M ≥ 3`). -/
theorem k2KarNorm_sndKer_conj_C (hM : 3 ≤ M) (k l : Fin M) (hkl : k ≠ l)
    (t : Localization.Away s) {z : SteinbergGroup (Fin M) (Polynomial (Localization.Away s))}
    (hz : z ∈ k2KarInj_sndKer s M) :
    x k l hkl (Polynomial.C t) * z * (x k l hkl (Polynomial.C t))⁻¹ ∈ k2KarInj_sndKer s M :=
  (k2KarNorm_sndKer_normal hM).conj_mem z hz _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_sndKer_conj_C

/-- `S` is normalized by every root `x_kl(g)`, in particular those with `g(0) = 0` (`M ≥ 3`).
The hypothesis `g(0) = 0` is not needed, since `S` is normal. -/
theorem k2KarNorm_sndKer_conj_root (hM : 3 ≤ M) (k l : Fin M) (hkl : k ≠ l)
    (g : Polynomial (Localization.Away s))
    {z : SteinbergGroup (Fin M) (Polynomial (Localization.Away s))}
    (hz : z ∈ k2KarInj_sndKer s M) :
    x k l hkl g * z * (x k l hkl g)⁻¹ ∈ k2KarInj_sndKer s M :=
  (k2KarNorm_sndKer_normal hM).conj_mem z hz _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_sndKer_conj_root

/-- `normalClosure {x_ij(h) : h(0) = 0} ≤ S` (`M ≥ 3`). -/
theorem k2KarNorm_normalClosure_le_sndKer (hM : 3 ≤ M) :
    Subgroup.normalClosure (k2KarNorm_polyGens (Fin M) (Localization.Away s)) ≤
      k2KarInj_sndKer s M := by
  haveI := k2KarNorm_sndKer_normal (s := s) hM
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨i, j, hij, h, h0, rfl⟩
  exact k2KarInj_x_mem i j hij h0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_normalClosure_le_sndKer

/-- **`q : ker fst → ker ev₀`, `y ↦ snd y`, is surjective** (`M ≥ 3`). -/
theorem k2KarNorm_q_surjective (hM : 3 ≤ M) : Function.Surjective (k2Karoubi_q s M) := by
  rintro ⟨z, hz⟩
  have hz' : z ∈ k2KarInj_sndKer s M := by
    rw [k2KarNorm_sndKer_eq_kerB hM]
    exact hz
  obtain ⟨y, hy, rfl⟩ := k2KarInj_mem_sndKer.mp hz'
  exact ⟨⟨y, hy⟩, Subtype.ext rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_q_surjective

end KarNormSnd

end GroupApproximation.BooneHigman.Metabelian.ElemFP
