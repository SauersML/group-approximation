import GroupApproximation.Manuscript.SimpleKazhdanSofic.CrossedProductSiteAction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordNormalForm
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.Cylinders
import GroupApproximation.Meta.AxiomGuard

/-!
# Full-group elements as elements of `LC(X, F₂) ⋊ ℤ`, through the site action

The crossed product `R = LC(X, F₂) ⋊ ℤ` acts faithfully on `F₂^{(X × ℤ)}` (`SiteAction.rho`):
`f δ_{x,t} = f(T^t x) δ_{x,t}` and `u δ_{x,t} = δ_{x,t+1}`. Read `δ_{x,t}` as the point `T^t x` of
the orbit of `x`. An element `e ∈ R` *represents* a permutation `g` (`SiteRep T e g`) if it moves
every site as `g` moves the point: `e δ_{x,t} = δ_{x,t+j}` where `g (T^t x) = T^{t+j} x`.

* `SiteRep.one`, `SiteRep.mul`: representations multiply.
* `SiteRep.eq_one_iff`: for an aperiodic `T`, a representing element is `1` iff the permutation is
  (`rho` is faithful).
* `siteRep_towerTable`: the tower permutation of a cylinder base `B` is represented by the table
  `towerTable cB σ`. It is `1 + Σ_i 1_{T^i B} + Σ_i 1_{T^{σ i} B} u^{σ i - i}` in characteristic `2`,
  so off the tower it is `1`, and at level `i` it is `u^{σ i - i}`.
-/

namespace GroupApproximation.Full.SKTFG

open GroupApproximation.SimpleKazhdanSofic GroupApproximation.CylinderTables
open GroupApproximation.Full.StepanovMatui.Matui
open SymbolicDynamics.FullShift
open Multiplicative (ofAdd toAdd)

section General

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)

/-- `e` moves each site `δ_{x,t}` as `g` moves the point `T^t x`. -/
def SiteRep (e : ClopenCrossedProduct T (ZMod 2)) (g : Equiv.Perm X) : Prop :=
  ∀ (x : X) (t : ℤ) (c : ZMod 2), ∃ j : ℤ, g ((T ^ t) x) = (T ^ (t + j)) x ∧
    SiteAction.rho T (ZMod 2) e (Finsupp.single (x, t) c) = Finsupp.single (x, t + j) c

theorem SiteRep.one : SiteRep T 1 1 := fun x t c =>
  ⟨0, by rw [add_zero, Equiv.Perm.one_apply], by rw [map_one, Module.End.one_apply, add_zero]⟩

theorem SiteRep.mul {e e' : ClopenCrossedProduct T (ZMod 2)} {g g' : Equiv.Perm X}
    (h : SiteRep T e g) (h' : SiteRep T e' g') : SiteRep T (e * e') (g * g') := by
  intro x t c
  obtain ⟨j', hg', he'⟩ := h' x t c
  obtain ⟨j, hg, he⟩ := h x (t + j') c
  refine ⟨j' + j, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hg', hg, add_assoc]
  · rw [map_mul, Module.End.mul_apply, he', he, add_assoc]

theorem SiteRep.eq_one_iff {e : ClopenCrossedProduct T (ZMod 2)} {g : Equiv.Perm X}
    (hfree : ∀ j : ℤ, j ≠ 0 → ∀ y : X, (T ^ j) y ≠ y) (h : SiteRep T e g) :
    e = 1 ↔ g = 1 := by
  constructor
  · rintro rfl
    refine Equiv.ext fun y => ?_
    obtain ⟨j, hg, he⟩ := h y 0 1
    rw [map_one, Module.End.one_apply] at he
    have hj : j = 0 := by
      have := congrArg Prod.snd (Finsupp.single_left_injective (one_ne_zero (α := ZMod 2)) he)
      simp only [zero_add] at this
      exact this.symm
    rw [zpow_zero, Homeomorph.one_apply, hj, zero_add, zpow_zero, Homeomorph.one_apply] at hg
    rw [Equiv.Perm.one_apply]
    exact hg
  · rintro rfl
    apply SiteAction.rho_injective T (ZMod 2)
    rw [map_one]
    refine Finsupp.lhom_ext fun p c => ?_
    obtain ⟨x, t⟩ := p
    obtain ⟨j, hg, he⟩ := h x t c
    have hj : j = 0 := by
      by_contra hj
      apply hfree j hj ((T ^ t) x)
      rw [Equiv.Perm.one_apply] at hg
      rw [← Homeomorph.mul_apply, ← zpow_add, add_comm, ← hg]
    rw [he, hj, add_zero, Module.End.one_apply]

end General

/-! ## Tables over a subshift -/

section Subshift

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A]
  (S : Subshift A ℤ)

omit [DecidableEq A] in
/-- `ρ(1_c u^j) δ_{x,t} = 1_c(T^{t+j} x) δ_{x,t+j}`. -/
theorem rho_monoEval (m : Mono A) (x : S.carrier) (t : ℤ) (c : ZMod 2) :
    SiteAction.rho (SimpleKazhdanSofic.subshiftHomeo S) (ZMod 2)
        (monoEval (SimpleKazhdanSofic.subshiftHomeo S) m) (Finsupp.single (x, t) c) =
      Finsupp.single (x, t + m.1)
        (cylInd S.carrier m.2 ((SimpleKazhdanSofic.subshiftHomeo S ^ (t + m.1)) x) * c) := by
  rw [monoEval, SiteAction.rho_single, Module.End.mul_apply, SiteAction.shiftHom_apply,
    SiteAction.shiftLin_single, SiteAction.coeffHom_apply, SiteAction.diag_single]
  rfl

/-- The tower table of a cylinder `cB` and `σ ∈ Perm (Fin 5)`:
`1 + Σ_i 1_{T^i B} + Σ_i 1_{T^{σ i} B} u^{σ i - i}`. -/
def towerTable (cB : Cyl A) (σ : Equiv.Perm (Fin 5)) : Table A :=
  ((0 : ℤ), ([] : Cyl A)) ::
    ((List.finRange 5).map fun i : Fin 5 => ((0 : ℤ), cylShift (-((i : ℕ) : ℤ)) cB)) ++
    (List.finRange 5).map fun i : Fin 5 =>
      ((((σ i : Fin 5) : ℕ) : ℤ) - ((i : ℕ) : ℤ), cylShift (-(((σ i : Fin 5) : ℕ) : ℤ)) cB)

omit [DecidableEq A] in
theorem eval_map_finRange (f : Fin 5 → Mono A) :
    eval (SimpleKazhdanSofic.subshiftHomeo S) ((List.finRange 5).map f) =
      ∑ i : Fin 5, monoEval (SimpleKazhdanSofic.subshiftHomeo S) (f i) := by
  rw [eval, List.map_map, Fin.sum_univ_def]
  rfl

/-- Level `l` of the tower over the cylinder `cB`. -/
theorem cylInd_cylShift_zpow (cB : Cyl A) (l s : ℤ) (x : S.carrier) :
    cylInd S.carrier (cylShift (-l) cB) ((SimpleKazhdanSofic.subshiftHomeo S ^ s) x) =
      if cylMem cB ((SimpleKazhdanSofic.subshiftHomeo S ^ (s - l)) x).1 then 1 else 0 := by
  rw [cylInd_apply]
  congr 1
  apply propext
  rw [cylMem_cylShift]
  have e : (fun i => ((SimpleKazhdanSofic.subshiftHomeo S ^ s) x).1 (i + -l)) =
      ((SimpleKazhdanSofic.subshiftHomeo S ^ (s - l)) x).1 := by
    funext i
    rw [subshiftHomeo_zpow_val, subshiftHomeo_zpow_val]
    exact congrArg x.1 (by ring)
  rw [e]

omit [DiscreteTopology A] [DecidableEq A] in
theorem single_add_self (p : S.carrier × ℤ) (c : ZMod 2) :
    Finsupp.single p c + Finsupp.single p c = 0 := by
  rw [← Finsupp.single_add, show c + c = 0 by fin_cases c <;> rfl, Finsupp.single_zero]

/-- **The tower table represents the tower permutation.** -/
theorem siteRep_towerTable {cB : Cyl A} {B : Set S.carrier}
    (hcB : ∀ y : S.carrier, y ∈ B ↔ cylMem cB y.1)
    (hd : TowerDisj (SimpleKazhdanSofic.subshiftHomeo S).toEquiv B 4) (σ : Equiv.Perm (Fin 5)) :
    SiteRep (SimpleKazhdanSofic.subshiftHomeo S)
      (eval (SimpleKazhdanSofic.subshiftHomeo S) (towerTable cB σ))
      (towerPerm (SimpleKazhdanSofic.subshiftHomeo S).toEquiv B (towerLevels 4) hd σ) := by
  intro x t c
  set T := SimpleKazhdanSofic.subshiftHomeo S
  have hlev : ∀ l : Fin 5, (T.toEquiv ^ (-towerLevels 4 l)) ((T ^ t) x) ∈ B ↔
      cylMem cB ((T ^ (t - ((l : ℕ) : ℤ))) x).1 := by
    intro l
    rw [toEquiv_zpow_apply, zpow_apply_zpow_apply, hcB, towerLevels_val, neg_add_eq_sub]
  -- the three parts of the table
  have hsum : SiteAction.rho T (ZMod 2) (eval T (towerTable cB σ)) (Finsupp.single (x, t) c) =
      Finsupp.single (x, t) c +
      (∑ l : Fin 5, Finsupp.single (x, t)
        ((if cylMem cB ((T ^ (t - ((l : ℕ) : ℤ))) x).1 then (1 : ZMod 2) else 0) * c)) +
      ∑ l : Fin 5, Finsupp.single (x, t + ((((σ l : Fin 5) : ℕ) : ℤ) - ((l : ℕ) : ℤ)))
        ((if cylMem cB ((T ^ (t - ((l : ℕ) : ℤ))) x).1 then (1 : ZMod 2) else 0) * c) := by
    rw [towerTable, eval_append, eval_cons, eval_map_finRange S, eval_map_finRange S]
    simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply,
      rho_monoEval, add_zero, cylInd_nil, LocallyConstant.one_apply, one_mul]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [cylInd_cylShift_zpow]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [cylInd_cylShift_zpow,
        show t + ((((σ l : Fin 5) : ℕ) : ℤ) - ((l : ℕ) : ℤ)) - (((σ l : Fin 5) : ℕ) : ℤ) =
          t - ((l : ℕ) : ℤ) by ring]
  by_cases hin : ∃ i : Fin 5, (T.toEquiv ^ (-towerLevels 4 i)) ((T ^ t) x) ∈ B
  · obtain ⟨i, hi⟩ := hin
    have hone : ∀ l : Fin 5, cylMem cB ((T ^ (t - ((l : ℕ) : ℤ))) x).1 ↔ l = i := by
      intro l
      rw [← hlev]
      exact ⟨fun hl => hd l i _ hl hi, fun e => e ▸ hi⟩
    refine ⟨(((σ i : Fin 5) : ℕ) : ℤ) - ((i : ℕ) : ℤ), ?_, ?_⟩
    · have e : towerLevels 4 (σ i) - towerLevels 4 i + t =
          t + ((((σ i : Fin 5) : ℕ) : ℤ) - ((i : ℕ) : ℤ)) := by
        rw [towerLevels_val, towerLevels_val]
        ring
      rw [towerPerm_apply, towerFun_of_mem hd hi, toEquiv_zpow_apply, zpow_apply_zpow_apply, e]
    · rw [hsum, Finset.sum_eq_single i, Finset.sum_eq_single i]
      · rw [if_pos ((hone i).2 rfl), one_mul, single_add_self S, zero_add]
      · intro l _ hl
        rw [if_neg fun h => hl ((hone l).1 h), zero_mul, Finsupp.single_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
      · intro l _ hl
        rw [if_neg fun h => hl ((hone l).1 h), zero_mul, Finsupp.single_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
  · have hzero : ∀ l : Fin 5, ¬cylMem cB ((T ^ (t - ((l : ℕ) : ℤ))) x).1 := fun l hl =>
      hin ⟨l, (hlev l).2 hl⟩
    refine ⟨0, ?_, ?_⟩
    · rw [towerPerm_apply, towerFun_of_not hin, add_zero]
    · rw [hsum, add_zero]
      simp only [hzero, ↓reduceIte, zero_mul, Finsupp.single_zero, Finset.sum_const_zero,
        add_zero]

omit [DecidableEq A] in
theorem siteRep_unitTable :
    SiteRep (SimpleKazhdanSofic.subshiftHomeo S)
      (eval (SimpleKazhdanSofic.subshiftHomeo S) ([(0, [])] : Table A)) 1 := by
  rw [eval_unitTable]
  exact SiteRep.one _

end Subshift

end GroupApproximation.Full.SKTFG
