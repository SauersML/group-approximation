import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarNormConj
import GroupApproximation.Meta.AxiomGuard

/-!
# `H(J)`: conjugating `z_pq(a, r)` by roots other than `x_pq`

Lane `bh-met-92f`.  For `z_pq(a, r) = x_qp(r) x_pq(a) x_qp(r)⁻¹` (`a ∈ J`) and a root `x_kl(s)`
with `(k, l) ≠ (p, q)`, the conjugate lies in `H(J)`.  The cases are:
* `(k, l) = (q, p)`: the conjugate is `z_pq(a, s + r)`;
* `k = q`, `l ∉ {p, q}`: the conjugate is `(x_qp(r) x_pl(-(a s)) x_qp(r)⁻¹) · z_pq(a, r)`;
* `l = p`, `k ∉ {p, q}`: the conjugate is `(x_qp(r) x_kq(s a) x_qp(r)⁻¹) · z_pq(a, r)`;
* `k = p`, `l ∉ {p, q}`: the conjugate is `x_ql(-(r s))`-conjugation of `z_pq(a, r)`, which
  reduces to the second case;
* `l = q`, `k ∉ {p, q}`: the conjugate is `x_kp(s r)`-conjugation of `z_pq(a, r)`, which
  reduces to the third case;
* `{k, l} ∩ {p, q} = ∅`: the root commutes with both factors.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section KarNormRoots

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] {J : Ideal R}

/-- `(k, l) = (q, p)`: the conjugate is `z_pq(a, s + r)`. -/
theorem k2KarNorm_conj_z_opp (p q : ι) (hpq : p ≠ q) (s : R) {a : R} (ha : a ∈ J) (r : R) :
    x q p hpq.symm s * k2KarNorm_z p q hpq a r * (x q p hpq.symm s)⁻¹ ∈ k2KarNorm_H ι J := by
  have e : x q p hpq.symm s * k2KarNorm_z p q hpq a r * (x q p hpq.symm s)⁻¹ =
      k2KarNorm_z p q hpq a (s + r) := by
    rw [k2KarNorm_z, k2KarNorm_z, ← x_mul]
    group
  rw [e]
  exact k2KarNorm_z_mem p q hpq ha (s + r)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_z_opp

/-- `k = q`, `l ∉ {p, q}`. -/
theorem k2KarNorm_conj_z_right (p q l : ι) (hpq : p ≠ q) (hql : q ≠ l) (hpl : p ≠ l) (s : R)
    {a : R} (ha : a ∈ J) (r : R) :
    x q l hql s * k2KarNorm_z p q hpq a r * (x q l hql s)⁻¹ ∈ k2KarNorm_H ι J := by
  rw [k2KarNorm_z, k2KarNorm_conj_z3,
    k2KarNorm_conj_of_commute (x_commute_of_ne q l q p hql hpq.symm (Ne.symm hql) hpq s r),
    k2KarNorm_C1 p q l hpq hql hpl a s, k2KarNorm_conj_mul]
  exact mul_mem
    (k2KarNorm_conj_x q p hpq.symm r p l hpl (neg_mem (Ideal.mul_mem_right s J ha)))
    (k2KarNorm_z_mem p q hpq ha r)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_z_right

/-- `l = p`, `k ∉ {p, q}`. -/
theorem k2KarNorm_conj_z_left (p q k : ι) (hpq : p ≠ q) (hkp : k ≠ p) (hkq : k ≠ q) (s : R)
    {a : R} (ha : a ∈ J) (r : R) :
    x k p hkp s * k2KarNorm_z p q hpq a r * (x k p hkp s)⁻¹ ∈ k2KarNorm_H ι J := by
  rw [k2KarNorm_z, k2KarNorm_conj_z3,
    k2KarNorm_conj_of_commute (x_commute_of_ne k p q p hkp hpq.symm hpq (Ne.symm hkp) s r),
    k2KarNorm_C2 p q k hpq hkp hkq a s, k2KarNorm_conj_mul]
  exact mul_mem (k2KarNorm_conj_x q p hpq.symm r k q hkq (Ideal.mul_mem_left J s ha))
    (k2KarNorm_z_mem p q hpq ha r)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_z_left

/-- `k = p`, `l ∉ {p, q}`: reduces to `k2KarNorm_conj_z_right`. -/
theorem k2KarNorm_conj_z_rowp (p q l : ι) (hpq : p ≠ q) (hpl : p ≠ l) (hql : q ≠ l) (s : R)
    {a : R} (ha : a ∈ J) (r : R) :
    x p l hpl s * k2KarNorm_z p q hpq a r * (x p l hpl s)⁻¹ ∈ k2KarNorm_H ι J := by
  have e : x p l hpl s * k2KarNorm_z p q hpq a r * (x p l hpl s)⁻¹ =
      x q l hql (-(r * s)) * k2KarNorm_z p q hpq a r * (x q l hql (-(r * s)))⁻¹ := by
    rw [k2KarNorm_z, k2KarNorm_conj_z3, k2KarNorm_C1 q p l hpq.symm hpl hql r s,
      k2KarNorm_conj_of_commute (x_commute_of_ne p l p q hpl hpq (Ne.symm hpl) hpq.symm s a)]
    group
  rw [e]
  exact k2KarNorm_conj_z_right p q l hpq hql hpl _ ha r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_z_rowp

/-- `l = q`, `k ∉ {p, q}`: reduces to `k2KarNorm_conj_z_left`. -/
theorem k2KarNorm_conj_z_colq (p q k : ι) (hpq : p ≠ q) (hkp : k ≠ p) (hkq : k ≠ q) (s : R)
    {a : R} (ha : a ∈ J) (r : R) :
    x k q hkq s * k2KarNorm_z p q hpq a r * (x k q hkq s)⁻¹ ∈ k2KarNorm_H ι J := by
  have e : x k q hkq s * k2KarNorm_z p q hpq a r * (x k q hkq s)⁻¹ =
      x k p hkp (s * r) * k2KarNorm_z p q hpq a r * (x k p hkp (s * r))⁻¹ := by
    rw [k2KarNorm_z, k2KarNorm_conj_z3, k2KarNorm_C2 q p k hpq.symm hkq hkp r s,
      k2KarNorm_conj_of_commute (x_commute_of_ne k q p q hkq hpq hpq.symm (Ne.symm hkq) s a)]
    group
  rw [e]
  exact k2KarNorm_conj_z_left p q k hpq hkp hkq _ ha r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_z_colq

/-- `{k, l} ∩ {i, j} = ∅`: the root commutes with `z_ij(a, r)`. -/
theorem k2KarNorm_conj_z_far (k l : ι) (hkl : k ≠ l) (i j : ι) (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) (s : R) {a : R} (ha : a ∈ J) (r : R) :
    x k l hkl s * k2KarNorm_z i j hij a r * (x k l hkl s)⁻¹ ∈ k2KarNorm_H ι J := by
  rw [k2KarNorm_z, k2KarNorm_conj_z3,
    k2KarNorm_conj_of_commute (x_commute_of_ne k l j i hkl hij.symm hlj (Ne.symm hki) s r),
    k2KarNorm_conj_of_commute (x_commute_of_ne k l i j hkl hij hli (Ne.symm hkj) s a)]
  exact k2KarNorm_z_mem i j hij ha r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_z_far

end KarNormRoots

end GroupApproximation.BooneHigman.Metabelian.ElemFP
