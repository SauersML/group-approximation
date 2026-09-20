import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.FG
import GroupApproximation.Meta.AxiomGuard

/-!
# Matui's finite generation theorem for minimal subshifts

`derivedFullGroupSubshift_fg`: for an infinite minimal subshift `S` over a finite alphabet,
the derived topological full group `⁅[[σ]], [[σ]]⁆` is finitely generated (Matui 2006, Thm 5.4), so
`DerivedFullGroupSubshiftFGStatement` holds. See `SKTFG.FG` for the plan of the proof.
-/

namespace GroupApproximation.Full.SKTFG

open GroupApproximation.Full.StepanovMatui.Matui
open SymbolicDynamics.FullShift Equiv
open scoped commutatorElement

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ)

/-- **Three-cycles lie in any subgroup for which all long cylinders are good.** -/
theorem threeCycle_mem_of_good (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S)
    (G : Subgroup (Perm S.carrier)) (N : ℕ)
    (hgood : ∀ z : ℤ → A, ∀ a b : ℤ, a ≤ 0 → (N : ℤ) ≤ b → Good S G (cyl S z a b))
    {f : Perm S.carrier}
    (hf : haveI := SimpleKazhdanSofic.compactSpace_carrier S
      f ∈ fullGroup (SimpleKazhdanSofic.subshiftHomeo S))
    {U : Set S.carrier} (hU : IsClopen U) (hdat : IsThreeCycleDatum f U) :
    threeCycle f U ∈ G := by
  haveI := SimpleKazhdanSofic.compactSpace_carrier S
  haveI := hinf
  set T := SimpleKazhdanSofic.subshiftHomeo S
  have hmin' : SimpleKazhdanSofic.IsMinimalSystem T :=
    SimpleKazhdanSofic.minimalSubshift_dense_orbits S hmin
  refine threeCycle_mem_of_local hU hdat fun x hxU => ?_
  have hx1 : f x ≠ x := fun h => hdat.1 x hxU (by rw [h]; exact hxU)
  have hx2 : f (f x) ≠ x := fun h => hdat.2 x hxU (by rw [h]; exact hxU)
  obtain ⟨W, hWc, hxW, E, hE0, hdisj, h1, h2, -⟩ :=
    exists_local_eight_tower T hmin' isClopen_univ ⟨x, Set.mem_univ x⟩ hf hx1 hx2
  refine ⟨W, hWc, hxW, fun A' hA' hA'U hA'W => ?_⟩
  -- the exponents are distinct
  have hEinj : Function.Injective E := by
    intro i j hij
    refine hdisj W subset_rfl i j ((T.toEquiv ^ E i) x) ?_ ?_
    · rw [perm_zpow_apply_zpow_apply, neg_add_cancel, zpow_zero, Equiv.Perm.one_apply]
      exact hxW
    · rw [perm_zpow_apply_zpow_apply, hij, neg_add_cancel, zpow_zero, Equiv.Perm.one_apply]
      exact hxW
  -- the span of the three levels `0, E 1, E 2`
  set m : ℤ := min (min 0 (E 1)) (E 2)
  set Mx : ℤ := max (max 0 (E 1)) (E 2)
  have hm0 : m ≤ 0 := (min_le_left _ _).trans (min_le_left _ _)
  have hm1 : m ≤ E 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hm2 : m ≤ E 2 := min_le_right _ _
  have hM0 : 0 ≤ Mx := (le_max_left _ _).trans (le_max_left _ _)
  have hM1 : E 1 ≤ Mx := (le_max_right _ _).trans (le_max_left _ _)
  have hM2 : E 2 ≤ Mx := le_max_right _ _
  set K : ℕ := (Mx - m).toNat
  have hK : (K : ℤ) = Mx - m := Int.toNat_of_nonneg (by omega)
  have hE10 : E 1 ≠ 0 := fun h => by
    have := hEinj (h.trans hE0.symm)
    exact absurd this (by decide)
  have hK1 : 1 ≤ K := by omega
  obtain ⟨RK, hRK⟩ := exists_sepRadius S hinf hmin (K + 5)
  obtain ⟨rA, hrA⟩ := exists_cyl_radius S hA'
  set r : ℕ := rA + N + K + m.natAbs + RK with hr
  have hdatA : IsThreeCycleDatum f A' :=
    ⟨fun y hy h => hdat.1 y (hA'U hy) (hA'U h), fun y hy h => hdat.2 y (hA'U hy) (hA'U h)⟩
  refine threeCycle_mem_of_cyl S hdatA r (fun y hy => hrA y hy r (by omega)) fun y hy => ?_
  have hPW : cyl S y.1 (-(r : ℤ)) r ⊆ W := (hrA y hy r (by omega)).trans hA'W
  set P := cyl S y.1 (-(r : ℤ)) r
  have hdP := hdisj P hPW
  -- the three-cycle is a tower action on the eight levels
  have s1 : swapAlong f P = towerPerm T.toEquiv P E hdP (swap 0 1) :=
    swapAlong_eq_towerPerm hdP (i₀ := 0) (j := 1) hE0 (by decide) fun z hz => h1 z (hPW hz)
  have s2 : swapAlong (f * f) P = towerPerm T.toEquiv P E hdP (swap 0 2) :=
    swapAlong_eq_towerPerm hdP (i₀ := 0) (j := 2) hE0 (by decide) fun z hz => h2 z (hPW hz)
  have hthree :
      threeCycle f P = towerPerm T.toEquiv P E hdP ⁅swap (0 : Fin 8) 1, swap 0 2⁆ := by
    show ⁅swapAlong f P, swapAlong (f * f) P⁆ = _
    rw [s1, s2, map_commutatorElement]
  rw [hthree]
  -- restrict to the three levels `0, E 1, E 2`
  let E3 : Fin 3 → ℤ := fun i => E (Fin.castLE (by norm_num) i)
  have hd3 : ∀ i j z, (T.toEquiv ^ (-E3 i)) z ∈ P → (T.toEquiv ^ (-E3 j)) z ∈ P → i = j :=
    fun i j z hi hj => Fin.castLE_injective _ (hdP _ _ z hi hj)
  have hsub1 : towerPerm T.toEquiv P E3 hd3 ⁅swap (0 : Fin 3) 1, swap 0 2⁆ =
      towerPerm T.toEquiv P E hdP ⁅swap (0 : Fin 8) 1, swap 0 2⁆ :=
    towerPerm_eq_of_sub hd3 hdP (Fin.castLE (by norm_num)) 0 (fun i => (add_zero _).symm)
      (fun z => by rw [zpow_zero, Equiv.Perm.one_apply]) _ _ (by decide +kernel)
      (by decide +kernel)
  rw [← hsub1]
  have hc0 : E3 0 = 0 := hE0
  have hlo : ∀ i, m ≤ E3 i := by
    intro i
    fin_cases i
    · show m ≤ E3 0
      rw [hc0]
      exact hm0
    · exact hm1
    · exact hm2
  have hhi : ∀ i, E3 i ≤ Mx := by
    intro i
    fin_cases i
    · show E3 0 ≤ Mx
      rw [hc0]
      exact hM0
    · exact hM1
    · exact hM2
  -- lift to the tall tower over the translate `B' = T^m P`
  let e : Fin 3 → Fin (K + 1) := fun i =>
    ⟨(E3 i - m).toNat, by have := hlo i; have := hhi i; omega⟩
  have he_val : ∀ i, (((e i : Fin (K + 1)) : ℕ) : ℤ) = E3 i - m := fun i =>
    Int.toNat_of_nonneg (by have := hlo i; omega)
  have heinj : Function.Injective e := by
    intro i j hij
    have h := congrArg (fun k : Fin (K + 1) => ((k : ℕ) : ℤ)) hij
    simp only [he_val] at h
    exact Fin.castLE_injective _ (hEinj (by simpa [E3] using h))
  have hEe : ∀ i, towerLevels K (e i) = E3 i + -m := fun i => by
    rw [towerLevels_val, he_val]
    ring
  set B' := cyl S (fun n => y.1 (n - -m)) (-(r : ℤ) + -m) (r + -m)
  have hBP : ∀ z, z ∈ B' ↔ (T.toEquiv ^ (-m)) z ∈ P := fun z => mem_zpow_cyl_iff S (-m) z
  have hdK : TowerDisj T.toEquiv B' K :=
    towerDisj_of_sepK (cyl_sepK S (hRK.mono S (by omega)) (by omega))
  have h01 : e 0 ≠ e 1 := fun h => absurd (heinj h) (by decide)
  have h02 : e 0 ≠ e 2 := fun h => absurd (heinj h) (by decide)
  have h12 : e 1 ≠ e 2 := fun h => absurd (heinj h) (by decide)
  have hc3 : (⁅swap (0 : Fin 3) 1, swap 0 2⁆ : Perm (Fin 3)) 0 = 1 ∧
      (⁅swap (0 : Fin 3) 1, swap 0 2⁆ : Perm (Fin 3)) 1 = 2 ∧
      (⁅swap (0 : Fin 3) 1, swap 0 2⁆ : Perm (Fin 3)) 2 = 0 := by decide +kernel
  set σK : Perm (Fin (K + 1)) := swap (e 0) (e 2) * swap (e 0) (e 1) with hσK
  have hrel1 : ∀ i, σK (e i) = e ((⁅swap (0 : Fin 3) 1, swap 0 2⁆ : Perm (Fin 3)) i) := by
    intro i
    fin_cases i
    · show σK (e 0) = e ((⁅swap (0 : Fin 3) 1, swap 0 2⁆ : Perm (Fin 3)) 0)
      rw [hc3.1, hσK, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne h01.symm h12]
    · show σK (e 1) = e ((⁅swap (0 : Fin 3) 1, swap 0 2⁆ : Perm (Fin 3)) 1)
      rw [hc3.2.1, hσK, Perm.mul_apply, swap_apply_right, swap_apply_left]
    · show σK (e 2) = e ((⁅swap (0 : Fin 3) 1, swap 0 2⁆ : Perm (Fin 3)) 2)
      rw [hc3.2.2, hσK, Perm.mul_apply, swap_apply_of_ne_of_ne h02.symm h12.symm,
        swap_apply_right]
  have hrel2 : ∀ j, (∀ i, e i ≠ j) → σK j = j := by
    intro j hj
    rw [hσK, Perm.mul_apply, swap_apply_of_ne_of_ne (hj 0).symm (hj 1).symm,
      swap_apply_of_ne_of_ne (hj 0).symm (hj 2).symm]
  have hsub2 : towerPerm T.toEquiv P E3 hd3 ⁅swap (0 : Fin 3) 1, swap 0 2⁆ =
      towerPerm T.toEquiv B' (towerLevels K) hdK σK :=
    towerPerm_eq_of_sub hd3 hdK e (-m) hEe hBP _ σK hrel1 hrel2
  rw [hsub2]
  have hσalt : σK ∈ alternatingGroup (Fin (K + 1)) := by
    rw [Perm.mem_alternatingGroup, hσK, Perm.sign_mul, Perm.sign_swap h02, Perm.sign_swap h01]
    exact Int.units_mul_self _
  -- the consecutive three-cycles of the tall tower
  have hle : Subgroup.closure (consSet K) ≤
      G.comap (towerPerm T.toEquiv B' (towerLevels K) hdK) := by
    rw [Subgroup.closure_le]
    rintro τ ⟨i, j, hij, rfl⟩
    show towerPerm T.toEquiv B' (towerLevels K) hdK (adjSwap i * adjSwap j) ∈ G
    have hiK : (i : ℕ) + 2 ≤ K := by have := j.isLt; omega
    set B'' := cyl S (fun n => (fun n => y.1 (n - -m)) ((i : ℤ) + n))
      ((-(r : ℤ) + -m) - i) ((r + -m) - i)
    have hBB : ∀ z, z ∈ B' ↔ (T.toEquiv ^ ((i : ℕ) : ℤ)) z ∈ B'' :=
      fun z => mem_cyl_zpow_iff S ((i : ℕ) : ℤ) z
    have hd2 : TowerDisj T.toEquiv B'' 2 :=
      towerDisj_of_sepK (cyl_sepK S (hRK.mono S (by omega)) (by omega))
    have hd4 : TowerDisj T.toEquiv B'' 4 :=
      towerDisj_of_sepK (cyl_sepK S (hRK.mono S (by omega)) (by omega))
    let e' : Fin 3 → Fin (K + 1) := fun t => ⟨(i : ℕ) + t, by have := t.isLt; omega⟩
    have he'0 : e' 0 = i.castSucc := Fin.ext (show (i : ℕ) + 0 = (i : ℕ) by omega)
    have he'1 : e' 1 = i.succ := Fin.ext (show (i : ℕ) + 1 = (i : ℕ) + 1 by omega)
    have he'2 : e' 2 = j.succ := Fin.ext (show (i : ℕ) + 2 = (j : ℕ) + 1 by omega)
    set c3' : Perm (Fin 3) :=
      adjSwap (⟨0, by norm_num⟩ : Fin 2) * adjSwap (⟨1, by norm_num⟩ : Fin 2) with hc3'
    have hv3 : c3' 0 = 1 ∧ c3' 1 = 2 ∧ c3' 2 = 0 := by rw [hc3']; decide +kernel
    have hr1 : ∀ t, (adjSwap i * adjSwap j) (e' t) = e' (c3' t) := by
      intro t
      fin_cases t
      · show (adjSwap i * adjSwap j) (e' 0) = e' (c3' 0)
        rw [hv3.1, he'0, he'1, cons_apply_castSucc hij]
      · show (adjSwap i * adjSwap j) (e' 1) = e' (c3' 1)
        rw [hv3.2.1, he'1, he'2, cons_apply_succ hij]
      · show (adjSwap i * adjSwap j) (e' 2) = e' (c3' 2)
        rw [hv3.2.2, he'2, he'0, cons_apply_jsucc hij]
    have hr2 : ∀ x, (∀ t, e' t ≠ x) → (adjSwap i * adjSwap j) x = x := by
      intro x hx
      refine cons_apply_of_ne hij ?_ ?_ ?_
      · rw [← he'0]; exact (hx 0).symm
      · rw [← he'1]; exact (hx 1).symm
      · rw [← he'2]; exact (hx 2).symm
    have hsub3 : towerPerm T.toEquiv B'' (towerLevels 2) hd2 c3' =
        towerPerm T.toEquiv B' (towerLevels K) hdK (adjSwap i * adjSwap j) :=
      towerPerm_eq_of_sub hd2 hdK e' ((i : ℕ) : ℤ)
        (fun t => by
          rw [towerLevels_val, towerLevels_val]
          show ((((i : ℕ) + (t : ℕ) : ℕ)) : ℤ) = ((t : ℕ) : ℤ) + ((i : ℕ) : ℤ)
          push_cast
          ring) hBB c3' _ hr1 hr2
    have hsub4 : towerPerm T.toEquiv B'' (towerLevels 2) hd2 c3' =
        towerPerm T.toEquiv B'' (towerLevels 4) hd4
          (adjSwap (⟨0, by norm_num⟩ : Fin 4) * adjSwap (⟨1, by norm_num⟩ : Fin 4)) :=
      towerPerm_eq_of_sub hd2 hd4 (Fin.castLE (by norm_num)) 0
        (fun t => by rw [towerLevels_val, towerLevels_val, Fin.val_castLE, add_zero])
        (fun z => by rw [zpow_zero, Equiv.Perm.one_apply]) c3' _
        (by rw [hc3']; decide +kernel) (by decide +kernel)
    rw [← hsub3, hsub4]
    exact hgood _ _ _ (by omega) (by omega) hd4 _
      (closure_consSet_le_alternatingGroup 4
        (Subgroup.subset_closure ⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, rfl, rfl⟩))
  exact hle (alternatingGroup_le_closure_consSet K hK1 hσalt)

/-- **Matui's theorem** (Internat. J. Math. 2006, Thm 5.4), for a separation radius `R`: the
derived topological full group is generated by `gens S (2R + 1)`. -/
theorem derivedFullGroupSubshift_eq_closure_gens_of_sepRadius (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S) {R : ℕ} (hR : SepRadius S 5 R) :
    derivedFullGroupSubshift S = Subgroup.closure (gens S (2 * R + 1)) := by
  haveI := SimpleKazhdanSofic.compactSpace_carrier S
  haveI := hinf
  have hright := good_right S hR le_rfl (le_refl (2 * R + 1)) (good_base S (2 * R + 1))
  have hleft := good_left S hR le_rfl (le_refl (2 * R + 1)) hright
  have hgood : ∀ z : ℤ → A, ∀ a b : ℤ, a ≤ 0 → ((2 * R + 1 : ℕ) : ℤ) ≤ b →
      Good S (Subgroup.closure (gens S (2 * R + 1))) (cyl S z a b) := by
    intro z a b ha hb
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, a = -(j : ℤ) := ⟨(-a).toNat, by omega⟩
    exact hleft j z b hb
  have hmin' : SimpleKazhdanSofic.IsMinimalSystem (SimpleKazhdanSofic.subshiftHomeo S) :=
    SimpleKazhdanSofic.minimalSubshift_dense_orbits S hmin
  apply le_antisymm
  · show ⁅fullGroup (SimpleKazhdanSofic.subshiftHomeo S),
      fullGroup (SimpleKazhdanSofic.subshiftHomeo S)⁆ ≤ _
    rw [commutator_fullGroup_eq_alternatingFullGroup _ hmin', alternatingFullGroup,
      Subgroup.closure_le]
    rintro σ ⟨f, hf, U, hU, hdat, rfl⟩
    exact threeCycle_mem_of_good S hinf hmin _ (2 * R + 1) hgood hf hU hdat
  · rw [Subgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    rw [genPerm]
    split_ifs with h
    · exact good_derived S (isClopen_cylW S _ p.1) h p.2.1 p.2.2
    · exact (derivedFullGroupSubshift S).one_mem

/-- **Matui's theorem** (Internat. J. Math. 2006, Thm 5.4): the derived topological full group of
an infinite minimal subshift over a finite alphabet is finitely generated. -/
theorem derivedFullGroupSubshift_eq_closure_gens (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S) :
    ∃ N : ℕ, derivedFullGroupSubshift S = Subgroup.closure (gens S N) := by
  obtain ⟨R, hR⟩ := exists_sepRadius S hinf hmin 5
  exact ⟨2 * R + 1, derivedFullGroupSubshift_eq_closure_gens_of_sepRadius S hinf hmin hR⟩

theorem derivedFullGroupSubshift_fg (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S) : Group.FG ↥(derivedFullGroupSubshift S) := by
  obtain ⟨N, hDG⟩ := derivedFullGroupSubshift_eq_closure_gens S hinf hmin
  rw [Group.fg_iff_subgroup_fg, hDG]
  exact ⟨(gens_finite S N).toFinset, by rw [Set.Finite.coe_toFinset]⟩

/-- `DerivedFullGroupSubshiftFGStatement` holds: the finite generation input of SK row
`e5932a45f053`. -/
theorem derivedFullGroupSubshiftFGStatement_holds : DerivedFullGroupSubshiftFGStatement :=
  fun _ _ _ _ S hinf hmin => derivedFullGroupSubshift_fg S hinf hmin

end GroupApproximation.Full.SKTFG

#audit_axioms GroupApproximation.Full.SKTFG.derivedFullGroupSubshift_fg
#audit_closed_axioms GroupApproximation.Full.SKTFG.derivedFullGroupSubshiftFGStatement_holds
