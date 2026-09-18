import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWideStab
import GroupApproximation.Meta.AxiomGuard

/-!
# The wide Nagao step, part 3: multi-coordinate Euclidean reduction

Lane `bh-met-93l`.  Notation of `ElemFPK2PolyNagaoWideStab`; `J = K \ {m}`.

* `k2PolyNagaoWide_nu f = natDegree f + 1` (`0` at `f = 0`), and
  `k2PolyNagaoWide_mu K m v = 2 ∑_{j ∈ J} ν(v j) + ν(v m)`.
* `k2PolyNagaoWide_step`: if some `v j ≠ 0` (`j ∈ J`), one root element of `S_K` lowers `μ`:
  `x_jm(-1) x_mj(1)` when `v m = 0`; `x_jm(-(v j / v m))` when `ν(v m) ≤ ν(v j)`;
  `x_mj(-(v m / v j))` otherwise.
* `k2PolyNagaoWide_clear`: some `s ∈ S_K` clears every `J`-coordinate (strong induction on `μ`).
* `k2PolyNagaoWide_rep_exists`: every `v` in the orbit `G e_L` is `q r` with `q ∈ S_K ≤ Q` and
  `r` supported on `{m, L}`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act act_mul
  act_one act_x_apply unitVec unitVec_apply x_mem_rootSpan act_apply_of_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

open Classical in
/-- `ν f = natDegree f + 1` for `f ≠ 0`, and `ν 0 = 0`. -/
noncomputable def k2PolyNagaoWide_nu (f : Polynomial (ZMod p)) : ℕ :=
  if f = 0 then 0 else f.natDegree + 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_nu

/-- `μ v = 2 ∑_{j ∈ K \ {m}} ν(v j) + ν(v m)`. -/
noncomputable def k2PolyNagaoWide_mu (K : Finset I) (m : I) (v : I → Polynomial (ZMod p)) : ℕ :=
  2 * ∑ i ∈ K.erase m, k2PolyNagaoWide_nu (v i) + k2PolyNagaoWide_nu (v m)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_mu

theorem k2PolyNagaoWide_nu_zero : k2PolyNagaoWide_nu (0 : Polynomial (ZMod p)) = 0 := by
  unfold k2PolyNagaoWide_nu
  rw [if_pos rfl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_nu_zero

theorem k2PolyNagaoWide_nu_pos {f : Polynomial (ZMod p)} (hf : f ≠ 0) :
    0 < k2PolyNagaoWide_nu f := by
  unfold k2PolyNagaoWide_nu
  rw [if_neg hf]
  exact Nat.succ_pos _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_nu_pos

/-- `ν(f % g) < ν g` for `g ≠ 0`. -/
theorem k2PolyNagaoWide_nu_mod_lt (f : Polynomial (ZMod p)) {g : Polynomial (ZMod p)}
    (hg : g ≠ 0) : k2PolyNagaoWide_nu (f % g) < k2PolyNagaoWide_nu g := by
  unfold k2PolyNagaoWide_nu
  rw [if_neg hg]
  by_cases h : f % g = 0
  · rw [if_pos h]
    exact Nat.succ_pos _
  · rw [if_neg h]
    exact Nat.succ_lt_succ (Polynomial.natDegree_lt_natDegree h (Polynomial.degree_mod_lt f hg))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_nu_mod_lt

/-- `μ` drops if only the `j`- and `m`-coordinates change and their weighted `ν` drops. -/
theorem k2PolyNagaoWide_mu_lt {K : Finset I} {m j : I} (hj : j ∈ K.erase m)
    {v u : I → Polynomial (ZMod p)} (hu : ∀ i, i ≠ j → i ≠ m → u i = v i)
    (h : 2 * k2PolyNagaoWide_nu (u j) + k2PolyNagaoWide_nu (u m) <
      2 * k2PolyNagaoWide_nu (v j) + k2PolyNagaoWide_nu (v m)) :
    k2PolyNagaoWide_mu K m u < k2PolyNagaoWide_mu K m v := by
  have e1 : k2PolyNagaoWide_nu (u j) + ∑ i ∈ (K.erase m).erase j, k2PolyNagaoWide_nu (u i) =
      ∑ i ∈ K.erase m, k2PolyNagaoWide_nu (u i) := Finset.add_sum_erase _ _ hj
  have e2 : k2PolyNagaoWide_nu (v j) + ∑ i ∈ (K.erase m).erase j, k2PolyNagaoWide_nu (v i) =
      ∑ i ∈ K.erase m, k2PolyNagaoWide_nu (v i) := Finset.add_sum_erase _ _ hj
  have hs : ∑ i ∈ (K.erase m).erase j, k2PolyNagaoWide_nu (u i) =
      ∑ i ∈ (K.erase m).erase j, k2PolyNagaoWide_nu (v i) :=
    Finset.sum_congr rfl fun i hi => by
      rw [hu i (Finset.ne_of_mem_erase hi)
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi))]
  unfold k2PolyNagaoWide_mu
  rw [← e1, ← e2, hs]
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_mu_lt

/-- A single root element leaves every coordinate other than its row alone. -/
theorem k2PolyNagaoWide_act_x_ne {i j : I} (hij : i ≠ j) (c : Polynomial (ZMod p))
    (v : I → Polynomial (ZMod p)) {k : I} (hk : k ≠ i) : act (x i j hij c) v k = v k := by
  rw [act_x_apply, if_neg hk, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_act_x_ne

end GroupApproximation.BooneHigman.Metabelian.ElemFP
