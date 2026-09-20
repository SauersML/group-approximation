import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulXa
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's `X_{v,w}(a)`, its independence of the decomposition, and Lemma 1.3(a)

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, §1. Let `a` lie in the ideal of the
coordinates of `v`, say `a = u v`. Tulenbaev puts `X_{v,w}(a) = ∏_k X(v, a w_k)` whenever
`w = ∑_k w_k` with `w_k ⊥ v` having two zeros. He shows it is independent of the decomposition,
by comparing with the canonical pieces of `a w_k` for `u`.

Here (for `4 ≤ |I|`, under `IsLocal`):
* `Xa hX h4 v w u := ∏_{p,q} X(v, pc v w u p q)`. It is defined for all `v, w, u`.
* `prod_pc`, the grouping argument: `∏_{p,q} X(v, pc v x u p q) = X(v, (u v) x)` for `x ⊥ v`
  with two zeros.
* `Xa_eq_prod`: for `w = ∑_k w_k` as above, `Xa v w u = ∏_k X(v, (u v) w_k)`. This is Tulenbaev's
  definition, and in particular `Xa v w u` depends only on `u v`.
* `Xa_add`, `Xa_smul_u` and `Xa_lemma13a` (T 1.3(a)): `X_{v,bw}(a) X_{v,bw'}(a) = X_{v,w+w'}(ab)`.
* `Xa_pieces`: `X_{v,bw}(a)` for `b = u_b v` and any `w ⊥ v`, via the canonical pieces of `w`
  for `u_b`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TulElem

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (Elements)

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A] (hX : Elements I A)
  [Fact (IsLocal hX)]

omit [Fact (IsLocal hX)] in
theorem txc_congr {v x x' : I → A} (h : x = x') (hx : x ⬝ᵥ v = 0) (h2 : TwoZ x)
    (hx' : x' ⬝ᵥ v = 0) (h2' : TwoZ x') : txc hX hx h2 = txc hX hx' h2' := by
  subst h
  rfl

/-- `∏_p X(v, pc v x u p q) = X(v, (u_q v_q) x)` for `x ⊥ v` with two zeros. -/
theorem prod_pc_left (h4 : 4 ≤ Fintype.card I) {v x : I → A} (u : I → A) (hxv : x ⬝ᵥ v = 0)
    (hx2 : TwoZ x) (q : I) :
    ∏ p, txc hX (pc_dot v x u p q) (pc_twoZ h4 v x u p q) =
      txc hX (smul_dot (u q * v q) hxv) (hx2.smul (u q * v q)) := by
  obtain ⟨r, s, hrs, hr, hs⟩ := id hx2
  obtain ⟨l, hl, hlq⟩ : ∃ l, x l = 0 ∧ l ≠ q := by
    by_cases hq : q = r
    · exact ⟨s, hs, fun h => hrs (h.trans hq).symm⟩
    · exact ⟨r, hr, fun h => hq h.symm⟩
  apply Subtype.ext
  rw [coe_txc, ← tx_sum hX Finset.univ (fun p => pc v x u p q) (r := l)
    (fun p => pc_zero_of v u hl hlq p) (fun p => pc_dot v x u p q)
    (fun p => pc_twoZ h4 v x u p q), pc_sum_left u hxv q]

#audit_axioms prod_pc_left

/-- **The grouping argument**: `∏_{p,q} X(v, pc v x u p q) = X(v, (u v) x)` for `x ⊥ v` with two
zeros. -/
theorem prod_pc (h4 : 4 ≤ Fintype.card I) {v x : I → A} (u : I → A) (hxv : x ⬝ᵥ v = 0)
    (hx2 : TwoZ x) :
    ∏ pq : I × I, txc hX (pc_dot v x u pq.1 pq.2) (pc_twoZ h4 v x u pq.1 pq.2) =
      txc hX (smul_dot (u ⬝ᵥ v) hxv) (hx2.smul (u ⬝ᵥ v)) := by
  rw [Fintype.prod_prod_type_right,
    Finset.prod_congr rfl fun q _ => prod_pc_left hX h4 u hxv hx2 q]
  obtain ⟨r, -, -, hr, -⟩ := id hx2
  apply Subtype.ext
  rw [coe_txc, ← tx_sum hX Finset.univ (fun q => (u q * v q) • x) (r := r)
    (fun q => by simp [hr]) (fun q => smul_dot _ hxv) (fun q => hx2.smul _), ← Finset.sum_smul]
  rfl

#audit_axioms prod_pc

/-- **Tulenbaev's `X_{v,w}(a)`**, for `a = u v`: the product of the `X(v, pc v w u p q)`. -/
noncomputable def Xa (h4 : 4 ≤ Fintype.card I) (v w u : I → A) : SteinbergGroup I A :=
  ((∏ pq : I × I, txc hX (pc_dot v w u pq.1 pq.2) (pc_twoZ h4 v w u pq.1 pq.2) : Cv hX v) :
    SteinbergGroup I A)

/-- **Independence of the decomposition**: for `w = ∑_k w_k` with `w_k ⊥ v` having two zeros,
`X_{v,w}(u v) = ∏_k X(v, (u v) w_k)`. -/
theorem Xa_eq_prod (h4 : 4 ≤ Fintype.card I) (v u : I → A) {ι : Type*} (K : Finset ι)
    (ws : ι → I → A) (hv : ∀ k, ws k ⬝ᵥ v = 0) (h2 : ∀ k, TwoZ (ws k)) :
    Xa hX h4 v (∑ k ∈ K, ws k) u =
      ((∏ k ∈ K, txc hX (smul_dot (u ⬝ᵥ v) (hv k)) ((h2 k).smul (u ⬝ᵥ v)) : Cv hX v) :
        SteinbergGroup I A) := by
  have hfac : ∀ pq : I × I,
      txc hX (pc_dot v (∑ k ∈ K, ws k) u pq.1 pq.2) (pc_twoZ h4 v _ u pq.1 pq.2) =
        ∏ k ∈ K, txc hX (pc_dot v (ws k) u pq.1 pq.2) (pc_twoZ h4 v (ws k) u pq.1 pq.2) := by
    intro pq
    obtain ⟨l, -, -, hlp, hlq, -, -⟩ := exists_two_ne h4 pq.1 pq.2
    apply Subtype.ext
    rw [coe_txc, pc_sum, tx_sum hX K (fun k => pc v (ws k) u pq.1 pq.2) (r := l)
      (fun k => pc_apply_of_ne v (ws k) u hlp hlq) (fun k => pc_dot v (ws k) u pq.1 pq.2)
      (fun k => pc_twoZ h4 v (ws k) u pq.1 pq.2)]
  rw [Xa, Finset.prod_congr rfl fun pq _ => hfac pq, Finset.prod_comm,
    Finset.prod_congr rfl fun k _ => prod_pc hX h4 u (hv k) (h2 k)]

#audit_axioms Xa_eq_prod

/-- `X_{v,w}(a)` is additive in `w`. -/
theorem Xa_add (h4 : 4 ≤ Fintype.card I) (v w w' u : I → A) :
    Xa hX h4 v (w + w') u = Xa hX h4 v w u * Xa hX h4 v w' u := by
  have hfac : ∀ pq : I × I,
      txc hX (pc_dot v (w + w') u pq.1 pq.2) (pc_twoZ h4 v _ u pq.1 pq.2) =
        txc hX (pc_dot v w u pq.1 pq.2) (pc_twoZ h4 v w u pq.1 pq.2) *
          txc hX (pc_dot v w' u pq.1 pq.2) (pc_twoZ h4 v w' u pq.1 pq.2) := by
    intro pq
    obtain ⟨l, -, -, hlp, hlq, -, -⟩ := exists_two_ne h4 pq.1 pq.2
    apply Subtype.ext
    rw [coe_txc, Subgroup.coe_mul, coe_txc, coe_txc, pc_add,
      tx_add hX (pc_apply_of_ne v w u hlp hlq) (pc_apply_of_ne v w' u hlp hlq)
        (pc_dot v w u _ _) (pc_dot v w' u _ _)]
  rw [Xa, Xa, Xa, Finset.prod_congr rfl fun pq _ => hfac pq, Finset.prod_mul_distrib,
    Subgroup.coe_mul]

#audit_axioms Xa_add

omit [Fintype I] in
theorem pc_smul_u (v w u : I → A) (b : A) (p q : I) : pc v w (b • u) p q = pc v (b • w) u p q := by
  rw [pc, pc]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- `X_{v,w}(b a) = X_{v,bw}(a)`: `Xa v w (b u) = Xa v (b w) u`. -/
theorem Xa_smul_u (h4 : 4 ≤ Fintype.card I) (v w u : I → A) (b : A) :
    Xa hX h4 v w (b • u) = Xa hX h4 v (b • w) u := by
  rw [Xa, Xa]
  congr 1
  exact Finset.prod_congr rfl fun pq _ => txc_congr hX (pc_smul_u v w u b pq.1 pq.2) _ _ _ _

#audit_axioms Xa_smul_u

/-- **T Lemma 1.3(a)**: `X_{v,bw}(a) X_{v,bw'}(a) = X_{v,w+w'}(ab)`. -/
theorem Xa_lemma13a (h4 : 4 ≤ Fintype.card I) (v w w' u : I → A) (b : A) :
    Xa hX h4 v (b • w) u * Xa hX h4 v (b • w') u = Xa hX h4 v (w + w') (b • u) := by
  rw [← Xa_add, ← smul_add, Xa_smul_u]

#audit_axioms Xa_lemma13a

theorem pc_sum_all {v w : I → A} (u : I → A) (hw : w ⬝ᵥ v = 0) :
    ∑ pq : I × I, pc v w u pq.1 pq.2 = (u ⬝ᵥ v) • w := by
  rw [Fintype.sum_prod_type_right, Finset.sum_congr rfl fun q _ => pc_sum_left u hw q,
    ← Finset.sum_smul]
  rfl

attribute [local irreducible] Xa in
/-- `X_{v,bw}(a)` for `a = u_a v`, `b = u_b v` and any `w ⊥ v`, via the canonical pieces of `w`
for `u_b`. -/
theorem Xa_pieces (h4 : 4 ≤ Fintype.card I) {v w : I → A} (ua ub : I → A) (hw : w ⬝ᵥ v = 0) :
    Xa hX h4 v ((ub ⬝ᵥ v) • w) ua =
      ((∏ pq : I × I, txc hX (smul_dot (ua ⬝ᵥ v) (pc_dot v w ub pq.1 pq.2))
        ((pc_twoZ h4 v w ub pq.1 pq.2).smul (ua ⬝ᵥ v)) : Cv hX v) : SteinbergGroup I A) := by
  rw [← pc_sum_all ub hw]
  exact Xa_eq_prod hX h4 v ua (ι := I × I) Finset.univ (fun pq => pc v w ub pq.1 pq.2)
    (fun pq => pc_dot v w ub pq.1 pq.2) (fun pq => pc_twoZ h4 v w ub pq.1 pq.2)

#audit_axioms Xa_pieces

end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation
