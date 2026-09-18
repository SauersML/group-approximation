import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoJRedMove
import GroupApproximation.Meta.AxiomGuard

/-!
# The `J`-reduction of the root check, part 2: the Euclidean `J`-reduction

Lane `bh-met-94a`.  Notation of `ElemFPK2PolyNagaoJRedMove`.  Every move below is a root of
`Q^m`, so by `k2PolyNagaoJRed_transfer` the check moves backwards along it.

* `k2PolyNagaoJRed_step`: if two distinct `J`-coordinates `v j`, `v j'` are nonzero, one root
  `x_jj'(-(v j / v j'))` or `x_j'j(-(v j' / v j))` of `Q^m` lowers `μ`.
* `k2PolyNagaoJRed_reduce`: by strong induction on `μ`, the check at every orbit vector
  follows from the check at the orbit vectors with at most one nonzero `J`-coordinate.
* `k2PolyNagaoJRed_row`: the root `x_ij(-(v i / v j))` of `Q^m` replaces `v i` by `v i % v j`.
* `k2PolyNagaoJRed_normal`: if `v j` is the only nonzero `J`-coordinate, reducing rows `m` and
  `L` modulo `v j` gives the residual normal form.  This form is supported on `{m, L, j}`,
  with `v j ≠ 0`, `deg v_m < deg v_j` and `deg v_L < deg v_j`.
* `k2PolyNagaoJRed_check_all`: the check of `σ` at `x_mL(1)` follows from the supported case
  plus the normal-form case.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_x_apply
  unitVec)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- **One `J`-move.**  Two distinct nonzero `J`-coordinates: one root of `Q^m` lowers `μ`. -/
theorem k2PolyNagaoJRed_step {K : Finset I} {m : I} (L : I) {j j' : I} (hj : j ∈ K.erase m)
    (hj' : j' ∈ K.erase m) (hne : j ≠ j') {v : I → Polynomial (ZMod p)} (h1 : v j ≠ 0)
    (h2 : v j' ≠ 0) :
    ∃ g ∈ k2PolyNagaoWide_Qm p K m L,
      k2PolyNagaoWide_mu K m (act g v) < k2PolyNagaoWide_mu K m v := by
  have hjm : j ≠ m := Finset.ne_of_mem_erase hj
  have hj'm : j' ≠ m := Finset.ne_of_mem_erase hj'
  by_cases hle : k2PolyNagaoWide_nu (v j') ≤ k2PolyNagaoWide_nu (v j)
  · refine ⟨x j j' hne (-(v j / v j')), k2PolyNagaoJRed_x_mem_Qm hne _
      (Finset.mem_insert_of_mem (Finset.mem_of_mem_erase hj)) hj', ?_⟩
    refine k2PolyNagaoWide_mu_lt hj (fun i hij _ => k2PolyNagaoWide_act_x_ne _ _ _ hij) ?_
    have e1 : act (x j j' hne (-(v j / v j'))) v j = v j % v j' := by
      rw [act_x_apply, if_pos rfl]
      linear_combination -(EuclideanDomain.div_add_mod (v j) (v j'))
    rw [e1, k2PolyNagaoWide_act_x_ne _ _ _ hjm.symm]
    have hlt := k2PolyNagaoWide_nu_mod_lt (v j) h2
    omega
  · refine ⟨x j' j hne.symm (-(v j' / v j)), k2PolyNagaoJRed_x_mem_Qm hne.symm _
      (Finset.mem_insert_of_mem (Finset.mem_of_mem_erase hj')) hj, ?_⟩
    refine k2PolyNagaoWide_mu_lt hj' (fun i hij _ => k2PolyNagaoWide_act_x_ne _ _ _ hij) ?_
    have e1 : act (x j' j hne.symm (-(v j' / v j))) v j' = v j' % v j := by
      rw [act_x_apply, if_pos rfl]
      linear_combination -(EuclideanDomain.div_add_mod (v j') (v j))
    rw [e1, k2PolyNagaoWide_act_x_ne _ _ _ hj'm.symm]
    have hlt := k2PolyNagaoWide_nu_mod_lt (v j') h1
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_step

/-- **The `J`-reduction.**  By strong induction on `μ`, the check at every orbit vector
follows from the check at the orbit vectors with at most one nonzero `J`-coordinate. -/
theorem k2PolyNagaoJRed_reduce {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    (hbase : ∀ w : I → Polynomial (ZMod p), (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = w) →
      (∀ j ∈ K.erase m, ∀ j' ∈ K.erase m, w j ≠ 0 → w j' ≠ 0 → j = j') →
      k2PolyNagaoJRed_Chk p K m L hmL w)
    (n : ℕ) : ∀ v : I → Polynomial (ZMod p), k2PolyNagaoWide_mu K m v = n →
      (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) → k2PolyNagaoJRed_Chk p K m L hmL v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv
    by_cases hex : ∃ j ∈ K.erase m, ∃ j' ∈ K.erase m, v j ≠ 0 ∧ v j' ≠ 0 ∧ j ≠ j'
    · obtain ⟨j, hj, j', hj', h1, h2, hne⟩ := hex
      obtain ⟨g, hg, hlt⟩ := k2PolyNagaoJRed_step L hj hj' hne h1 h2
      have hgv := k2PolyNF_orbit_act
        (k2PolyNagaoWide_Q_le_G K L (k2PolyNagaoWide_Qm_le_Q K m L hg)) hv
      exact k2PolyNagaoJRed_transfer hmL hmK hLK hthird hStab hg hv
        (ih _ (by rw [← hn]; exact hlt) (act g v) rfl hgv)
    · exact hbase v hv (fun j hj j' hj' h1 h2 =>
        Classical.byContradiction fun hne => hex ⟨j, hj, j', hj', h1, h2, hne⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_reduce

/-- **Row reduction.**  The root `x_ij(-(v i / v j))` of `Q^m` replaces `v i` by `v i % v j`
and fixes every other coordinate. -/
theorem k2PolyNagaoJRed_row {K : Finset I} {m L i j : I} (hij : i ≠ j) (hi : i ∈ insert L K)
    (hj : j ∈ K.erase m) (v : I → Polynomial (ZMod p)) :
    ∃ g ∈ k2PolyNagaoWide_Qm p K m L,
      act g v i = v i % v j ∧ ∀ k, k ≠ i → act g v k = v k := by
  refine ⟨x i j hij (-(v i / v j)), k2PolyNagaoJRed_x_mem_Qm hij _ hi hj, ?_,
    fun k hk => k2PolyNagaoWide_act_x_ne _ _ _ hk⟩
  rw [act_x_apply, if_pos rfl]
  linear_combination -(EuclideanDomain.div_add_mod (v i) (v j))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_row

/-- **The normal form.**  If `v j` is the only nonzero `J`-coordinate of the orbit vector `v`,
the rows `m` and `L` reduced modulo `v j` give the residual normal form, and the check moves
back along both roots (`k2PolyNagaoJRed_transfer`). -/
theorem k2PolyNagaoJRed_normal {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    (hres : ∀ w : I → Polynomial (ZMod p), (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = w) →
      ∀ j ∈ K.erase m, (∀ k, k ≠ m → k ≠ L → k ≠ j → w k = 0) → w j ≠ 0 →
      (w m).degree < (w j).degree → (w L).degree < (w j).degree →
      k2PolyNagaoJRed_Chk p K m L hmL w)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v)
    (hone : ∀ j ∈ K.erase m, ∀ j' ∈ K.erase m, v j ≠ 0 → v j' ≠ 0 → j = j')
    {j : I} (hj : j ∈ K.erase m) (hvj : v j ≠ 0) : k2PolyNagaoJRed_Chk p K m L hmL v := by
  have hjm : j ≠ m := Finset.ne_of_mem_erase hj
  have hLj : L ≠ j := fun e => hLK (by rw [e]; exact Finset.mem_of_mem_erase hj)
  obtain ⟨g1, hG1, c1m, c1⟩ :=
    k2PolyNagaoJRed_row (L := L) hjm.symm (Finset.mem_insert_of_mem hmK) hj v
  have hv1 := k2PolyNF_orbit_act
    (k2PolyNagaoWide_Q_le_G K L (k2PolyNagaoWide_Qm_le_Q K m L hG1)) hv
  obtain ⟨g2, hG2, c2L, c2⟩ :=
    k2PolyNagaoJRed_row (m := m) hLj (Finset.mem_insert_self L K) hj (act g1 v)
  have hv2 := k2PolyNF_orbit_act
    (k2PolyNagaoWide_Q_le_G K L (k2PolyNagaoWide_Qm_le_Q K m L hG2)) hv1
  have hwj : act g2 (act g1 v) j = v j := by rw [c2 j hLj.symm, c1 j hjm]
  have hwm : act g2 (act g1 v) m = v m % v j := by rw [c2 m hmL, c1m]
  have hwL : act g2 (act g1 v) L = v L % v j := by rw [c2L, c1 L hmL.symm, c1 j hjm]
  refine k2PolyNagaoJRed_transfer hmL hmK hLK hthird hStab hG1 hv
    (k2PolyNagaoJRed_transfer hmL hmK hLK hthird hStab hG2 hv1
      (hres _ hv2 j hj (fun k hkm hkL hkj => ?_) ?_ ?_ ?_))
  · rw [c2 k hkL, c1 k hkm]
    by_cases hkK : k ∈ K
    · exact Classical.byContradiction fun hk0 =>
        hkj (hone k (Finset.mem_erase.2 ⟨hkm, hkK⟩) j hj hk0 hvj)
    · exact k2PolyNagaoJRed_orbit_out hv (fun h => (Finset.mem_insert.1 h).elim hkL hkK)
  · rw [hwj]
    exact hvj
  · rw [hwm, hwj]
    exact Polynomial.degree_mod_lt _ hvj
  · rw [hwL, hwj]
    exact Polynomial.degree_mod_lt _ hvj

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_normal

/-- **The `J`-reduction of the root check.**  The check of `σ` at `x_mL(1)` follows from the
check at the supported orbit vectors (`hsupp`) and at the residual normal forms (`hres`). -/
theorem k2PolyNagaoJRed_check_all {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    (hsupp : ∀ w : I → Polynomial (ZMod p), (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = w) →
      k2PolyNagaoWide_Supp m L w → k2PolyNagaoJRed_Chk p K m L hmL w)
    (hres : ∀ w : I → Polynomial (ZMod p), (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = w) →
      ∀ j ∈ K.erase m, (∀ k, k ≠ m → k ≠ L → k ≠ j → w k = 0) → w j ≠ 0 →
      (w m).degree < (w j).degree → (w L).degree < (w j).degree →
      k2PolyNagaoJRed_Chk p K m L hmL w) :
    k2PolyEuclid_Check p K L (k2PolyNagaoWide_sigma p K m L hmL)
      (x m L hmL (1 : Polynomial (ZMod p))) := by
  intro v hv
  refine k2PolyNagaoJRed_reduce hmL hmK hLK hthird hStab (fun w hw hone => ?_) _ v rfl hv
  by_cases hex : ∃ j ∈ K.erase m, w j ≠ 0
  · obtain ⟨j, hj, hwj⟩ := hex
    exact k2PolyNagaoJRed_normal hmL hmK hLK hthird hStab hres hw hone hj hwj
  · refine hsupp w hw (fun k hkm hkL => ?_)
    by_cases hkK : k ∈ K
    · exact Classical.byContradiction fun hk0 => hex ⟨k, Finset.mem_erase.2 ⟨hkm, hkK⟩, hk0⟩
    · exact k2PolyNagaoJRed_orbit_out hw (fun h => (Finset.mem_insert.1 h).elim hkL hkK)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRed_check_all

end GroupApproximation.BooneHigman.Metabelian.ElemFP
