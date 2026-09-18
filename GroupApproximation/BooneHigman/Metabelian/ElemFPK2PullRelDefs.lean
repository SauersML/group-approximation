import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullRelRing
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullRelGen
import GroupApproximation.Meta.AxiomGuard

/-!
# The relative subgroup and the action data

Lane `bh-met-91g`, definitions module.  Notation: `P = k2DilateSt_pullback s`, `L = A_s`,
`B = L[X]`.

* `k2PullRel_ker s M = ker (fst : St(M, P) → St(M, A))`, the relative subgroup.  It contains
  `x_ij(b)` for `fst b = 0` (`k2PullRel_x_mem`) and is stable under conjugation by
  `const(St(M, A))` (`k2PullRel_conj_mem_ker`).  It contains the relative generators of
  `ElemFPK2PullRelGen` (`k2PullRel_closure_le_ker`).
* For `q : k2PullRel_ker s M →* H`, `k2PullRel_u q i j hij h = q (x_ij (lift h))`.
* The action data for `α : St(M, L) →* MulAut H`:
  * `k2PullRel_F1`: `x_kl(t)` fixes `u_ij(h)` whenever `j ≠ k` and `l ≠ i`;
  * `k2PullRel_F2`: `x_ij(t) · u_jk(h) = u_ik(C t · h) · u_jk(h)`;
  * `k2PullRel_F3`: `x_jk(t) · u_ij(h) = u_ij(h) · u_ik(-(h · C t))`;
  * `k2PullRel_Compat`: on `λ(St(M, A))`, `α` is conjugation by `const`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section PullRelDefs

variable {A : Type*} [CommRing A] {s : A} {M : ℕ}

/-- The relative subgroup `ker (fst) ⊆ St(M, P)`. -/
def k2PullRel_ker (s : A) (M : ℕ) : Subgroup (SteinbergGroup (Fin M) (k2DilateSt_pullback s)) :=
  (ringMap (k2PullRel_fst s)).ker

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_ker

theorem k2PullRel_mem_ker {y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)} :
    y ∈ k2PullRel_ker s M ↔ ringMap (k2PullRel_fst s) y = 1 :=
  MonoidHom.mem_ker

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_mem_ker

theorem k2PullRel_ringMap_fst_const (c : SteinbergGroup (Fin M) A) :
    ringMap (k2PullRel_fst s) (ringMap (k2PullRel_const s) c) = c := by
  rw [ringMap_ringMap, k2PullRel_fst_comp_const, ringMap_id, MonoidHom.id_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_ringMap_fst_const

theorem k2PullRel_ringMap_snd_const (c : SteinbergGroup (Fin M) A) :
    ringMap (k2PullRel_snd s) (ringMap (k2PullRel_const s) c) =
      ringMap Polynomial.C (ringMap (algebraMap A (Localization.Away s)) c) := by
  rw [ringMap_ringMap, ringMap_ringMap, k2PullRel_snd_comp_const]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_ringMap_snd_const

theorem k2PullRel_x_mem (i j : Fin M) (hij : i ≠ j) {b : k2DilateSt_pullback s}
    (hb : k2PullRel_fst s b = 0) : x i j hij b ∈ k2PullRel_ker s M := by
  rw [k2PullRel_mem_ker, ringMap_x, hb, x_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_x_mem

theorem k2PullRel_x_lift_mem (i j : Fin M) (hij : i ≠ j)
    (h : Polynomial (Localization.Away s)) :
    x i j hij (k2PullRel_lift s h) ∈ k2PullRel_ker s M :=
  k2PullRel_x_mem i j hij (k2PullRel_fst_lift s h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_x_lift_mem

theorem k2PullRel_conj_mem_ker (c : SteinbergGroup (Fin M) A)
    {y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)} (hy : y ∈ k2PullRel_ker s M) :
    ringMap (k2PullRel_const s) c * y * (ringMap (k2PullRel_const s) c)⁻¹ ∈
      k2PullRel_ker s M := by
  rw [k2PullRel_mem_ker] at hy ⊢
  rw [map_mul, map_mul, map_inv, hy, k2PullRel_ringMap_fst_const, mul_one, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_conj_mem_ker

theorem k2PullRel_closure_le_ker :
    Subgroup.closure (k2PullRel_genSet (I := Fin M) (k2PullRel_const s) (k2PullRel_fst s)) ≤
      k2PullRel_ker s M := by
  rw [Subgroup.closure_le]
  rintro g ⟨d, i, j, hij, b, hb, rfl⟩
  exact k2PullRel_conj_mem_ker d (k2PullRel_x_mem i j hij hb)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_closure_le_ker

variable {H : Type*} [Group H]

/-- `u_ij(h) = q (x_ij (lift h))`, for `h ∈ L[X]`. -/
noncomputable def k2PullRel_u (q : k2PullRel_ker s M →* H) (i j : Fin M) (hij : i ≠ j)
    (h : Polynomial (Localization.Away s)) : H :=
  q ⟨x i j hij (k2PullRel_lift s h), k2PullRel_x_lift_mem i j hij h⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_u

/-- `x_kl(t)` fixes `u_ij(h)` when `j ≠ k` and `l ≠ i`. -/
def k2PullRel_F1 (q : k2PullRel_ker s M →* H)
    (α : SteinbergGroup (Fin M) (Localization.Away s) →* MulAut H) : Prop :=
  ∀ (i j k l : Fin M) (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i →
    ∀ (t : Localization.Away s) (h : Polynomial (Localization.Away s)),
      α (x k l hkl t) (k2PullRel_u q i j hij h) = k2PullRel_u q i j hij h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_F1

/-- `x_ij(t)` sends `u_jk(h)` to `u_ik(C t · h) · u_jk(h)`. -/
def k2PullRel_F2 (q : k2PullRel_ker s M →* H)
    (α : SteinbergGroup (Fin M) (Localization.Away s) →* MulAut H) : Prop :=
  ∀ (i j k : Fin M) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (t : Localization.Away s) (h : Polynomial (Localization.Away s)),
      α (x i j hij t) (k2PullRel_u q j k hjk h) =
        k2PullRel_u q i k hik (Polynomial.C t * h) * k2PullRel_u q j k hjk h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_F2

/-- `x_jk(t)` sends `u_ij(h)` to `u_ij(h) · u_ik(-(h · C t))`. -/
def k2PullRel_F3 (q : k2PullRel_ker s M →* H)
    (α : SteinbergGroup (Fin M) (Localization.Away s) →* MulAut H) : Prop :=
  ∀ (i j k : Fin M) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (t : Localization.Away s) (h : Polynomial (Localization.Away s)),
      α (x j k hjk t) (k2PullRel_u q i j hij h) =
        k2PullRel_u q i j hij h * k2PullRel_u q i k hik (-(h * Polynomial.C t))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_F3

/-- On `λ(St(M, A))`, `α` acts as conjugation by `const(St(M, A))`. -/
def k2PullRel_Compat (q : k2PullRel_ker s M →* H)
    (α : SteinbergGroup (Fin M) (Localization.Away s) →* MulAut H) : Prop :=
  ∀ (c : SteinbergGroup (Fin M) A) (i j : Fin M) (hij : i ≠ j) (b : k2DilateSt_pullback s)
    (hb : k2PullRel_fst s b = 0),
      α (ringMap (algebraMap A (Localization.Away s)) c)
          (q ⟨x i j hij b, k2PullRel_x_mem i j hij hb⟩) =
        q ⟨ringMap (k2PullRel_const s) c * x i j hij b * (ringMap (k2PullRel_const s) c)⁻¹,
          k2PullRel_conj_mem_ker c (k2PullRel_x_mem i j hij hb)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_Compat

end PullRelDefs

end GroupApproximation.BooneHigman.Metabelian.ElemFP
