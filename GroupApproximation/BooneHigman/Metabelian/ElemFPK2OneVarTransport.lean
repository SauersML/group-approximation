import GroupApproximation.BooneHigman.Metabelian.ElemFPK2Homotopy
import GroupApproximation.Meta.AxiomGuard

/-!
# Transport lemmas for the one-variable reduction of the nil part of `K₂(N, F_p[s_1..s_k])`

Lane `bh-met-22`, helper module.  These lemmas hold for arbitrary rings, with no hypothesis.

* `K2Map_K2Map`, `K2Map_id`, `K2Map_K2Map_of_comp_eq_id`: `K₂(I, -)` is a functor on ring maps
  (from `SteinbergBasic.ringMap_ringMap` and `SteinbergBasic.ringMap_id`);
* `K2MapEquiv`: a ring isomorphism induces a group isomorphism of unstable `K₂`;
* `K2IndexMap_castLEEmb_castLEEmb`, `K2IndexMap_eq_one_of_le`: padding in two steps is padding in
  one step, so an element that dies at rank `m` dies at every rank `M ≥ m`
  (from `Full.LVH2GL3.indexMap_castLEEmb_castLEEmb`);
* `evalRingHom_zero_comp_C`: `ev_{t=0} ∘ C = id` on `A[t]`;
* `constantCoeff_comp_finSuccEquiv`: under `MvPolynomial.finSuccEquiv R k :
  R[s_0..s_k] ≃ R[s_1..s_k][s_0]`, setting all variables to `0` is setting `s_0 = 0`, then the
  remaining variables to `0`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section RingTransport

variable {I R S T : Type*} [Fintype I] [DecidableEq I] [Ring R] [Ring S] [Ring T]

/-- `K₂(I, -)` respects composition of ring maps. -/
theorem K2Map_K2Map (g : S →+* T) (f : R →+* S) (u : K2 I R) :
    K2Map g (K2Map f u) = K2Map (g.comp f) u :=
  Subtype.ext (ringMap_ringMap g f (u : SteinbergGroup I R))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2Map_K2Map

/-- `K₂(I, -)` sends the identity ring map to the identity. -/
theorem K2Map_id (u : K2 I R) : K2Map (RingHom.id R) u = u :=
  Subtype.ext (DFunLike.congr_fun (ringMap_id (I := I) (R := R)) (u : SteinbergGroup I R))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2Map_id

/-- A left inverse of a ring map induces a left inverse on `K₂`. -/
theorem K2Map_K2Map_of_comp_eq_id (g : S →+* R) (f : R →+* S) (h : g.comp f = RingHom.id R)
    (u : K2 I R) : K2Map g (K2Map f u) = u := by
  rw [K2Map_K2Map, h, K2Map_id]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2Map_K2Map_of_comp_eq_id

/-- A ring isomorphism `R ≃+* S` induces a group isomorphism `K₂(I, R) ≃* K₂(I, S)`. -/
noncomputable def K2MapEquiv (e : R ≃+* S) : K2 I R ≃* K2 I S :=
  MonoidHom.toMulEquiv (K2Map e.toRingHom) (K2Map e.symm.toRingHom)
    (MonoidHom.ext fun u ↦ K2Map_K2Map_of_comp_eq_id _ _ e.symm_toRingHom_comp_toRingHom u)
    (MonoidHom.ext fun u ↦ K2Map_K2Map_of_comp_eq_id _ _ e.toRingHom_comp_symm_toRingHom u)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2MapEquiv

end RingTransport

section Padding

variable {R : Type*} [Ring R]

/-- Padding `Fin n ↪ Fin m ↪ Fin M` in two steps is padding in one step, on `K₂`. -/
theorem K2IndexMap_castLEEmb_castLEEmb {n m M : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ M) (u : K2n n R) :
    K2IndexMap (Fin.castLEEmb h₂) (K2IndexMap (Fin.castLEEmb h₁) u) =
      K2IndexMap (Fin.castLEEmb (h₁.trans h₂)) u :=
  Subtype.ext
    (GroupApproximation.Full.LVH2GL3.indexMap_castLEEmb_castLEEmb h₁ h₂ (u : St n R))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2IndexMap_castLEEmb_castLEEmb

/-- An element of `K₂(n, R)` that dies at rank `m` dies at every rank `M ≥ m`. -/
theorem K2IndexMap_eq_one_of_le {n m M : ℕ} (h₁ : n ≤ m) (hmM : m ≤ M) (h : n ≤ M)
    {u : K2n n R} (hu : K2IndexMap (Fin.castLEEmb h₁) u = 1) :
    K2IndexMap (Fin.castLEEmb h) u = 1 := by
  have h2 := K2IndexMap_castLEEmb_castLEEmb h₁ hmM u
  rw [hu, map_one] at h2
  exact h2.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2IndexMap_eq_one_of_le

end Padding

section Polynomial

variable {R : Type*} [CommRing R]

/-- `ev_{t=0} ∘ C = id` on `A[t]`. -/
theorem evalRingHom_zero_comp_C :
    (Polynomial.evalRingHom 0 : Polynomial R →+* R).comp Polynomial.C = RingHom.id R :=
  RingHom.ext fun a ↦ by
    rw [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C, RingHom.id_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.evalRingHom_zero_comp_C

/-- Pointwise form: the constant coefficient of `(finSuccEquiv f)(0)` is the constant coefficient
of `f`. -/
theorem constantCoeff_eval_zero_finSuccEquiv {k : ℕ} (f : MvPolynomial (Fin (k + 1)) R) :
    MvPolynomial.constantCoeff (Polynomial.eval 0 (MvPolynomial.finSuccEquiv R k f)) =
      MvPolynomial.constantCoeff f := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, MvPolynomial.constantCoeff_eq,
    MvPolynomial.constantCoeff_eq, MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_zero_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.constantCoeff_eval_zero_finSuccEquiv

/-- Setting all variables of `R[s_0..s_k]` to `0` factors as `finSuccEquiv`, then `s_0 = 0`, then
the remaining variables to `0`. -/
theorem constantCoeff_comp_finSuccEquiv (k : ℕ) :
    ((MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R).comp
        (Polynomial.evalRingHom 0)).comp (MvPolynomial.finSuccEquiv R k).toRingEquiv.toRingHom =
      MvPolynomial.constantCoeff :=
  RingHom.ext fun f ↦ constantCoeff_eval_zero_finSuccEquiv f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.constantCoeff_comp_finSuccEquiv

end Polynomial

end GroupApproximation.BooneHigman.Metabelian.ElemFP
