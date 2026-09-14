import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralTowerCopy
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimplicityNormalSubgroup
import GroupApproximation.Pestov91.SimpleModCentre
import Mathlib.Dynamics.Minimal

/-!
# Simplicity for group actions: from the commutator witness to `K = G`

`simple_kazhdan_sofic_group.tex` at 37551fd93, subsection "Simplicity" (l.197–208):

> Then $y=eI_3+(k-I_3)$ and $y'=eI_3+(k^{-1}-I_3)$ satisfy $yy'=y'y=eI_3$, so $k=(1-e)I_3+y\in H_V$.
> As $K\cap H_V$ is a nontrivial normal subgroup of $H_V\cong\GL_d(\F_2)=\PSL_d(\F_2)$, which is simple
> as $d\ge3$, we get $H_V\subseteq K$, and $e_{pq}(e_V)\in K$ for all $p\ne q$.
> Finally, $J=\{r\in R:e_{pq}(r)\in K\text{ for all }p\ne q\}$ is a two-sided ideal … It contains $e_V$,
> so it contains every $e_{\xi V}=u_\xi e_Vu_\xi^{-1}$. By minimality and compactness finitely many of
> these sets cover $Z$, so $1=1-\prod_i(1-e_{\xi_iV})\in J$. So $J=R$ and $K=G$.

Over a covariant pair `(coeff, u)`, for `EL_n(R)` with `n ≥ 3`:

* `exists_copyGL_eq`: `k ∈ H_V`, through `ChainRadical.exists_cornerUnitHom_eq` (printed `y y' = e I`);
* `epsilon_one_one`: `ε_ee = e_V`;
* `unit_mul_charFn_mul_inv`, `prod_one_sub_charFn_smul_eq_zero`, `one_mem_levelIdeal_of_smul_cover`:
  `e_{ξV} ∈ J` and `1 = 1 - ∏ᵢ(1 - e_{ξᵢV}) ∈ J`;
* `exists_finset_smul_cover`: minimality and compactness give the finite cover;
* `eq_top_of_generalCommutatorWitness`: `K = G`;
* `isSimpleGroup_of_generalCommutatorWitness` and the closed endpoint
  `printedGeneralSimplicityFromWitness`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace General

open Pointwise ChainRadical Pestov91.SimpleModCentre

variable {Λ Z R : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]
  [Ring R] {coeff : LocallyConstant Z (ZMod 2) →+* R} {u : Λ →* Rˣ}

/-- `ε_ee = e_V`. -/
theorem epsilon_one_one {V : Set Z} (hV : IsClopen V) :
    epsilon coeff u hV 1 1 = coeff (LocallyConstant.charFn (ZMod 2) hV) := by
  unfold epsilon
  rw [mul_inv_cancel, map_one, Units.val_one, mul_one]
  congr 1
  exact charFn_congr _ _ (one_smul Λ V)

/-- For a finite cover `Z = ⋃_{ξ ∈ s} ξV`: `∏_{ξ ∈ s} (1 - 1_{ξV}) = 0` in `LC(Z, F_2)`. -/
theorem prod_one_sub_charFn_smul_eq_zero {V : Set Z} (hV : IsClopen V) (s : Finset Λ)
    (hs : ∀ z : Z, ∃ ξ ∈ s, z ∈ ξ • V) :
    ∏ ξ ∈ s, (1 - LocallyConstant.charFn (ZMod 2) (isClopen_smul ξ hV)) = 0 := by
  ext z
  obtain ⟨ξ, hξ, hz⟩ := hs z
  have hc : ∀ f : LocallyConstant Z (ZMod 2),
      (f : Z → ZMod 2) = LocallyConstant.coeFnMonoidHom f := fun _ => rfl
  rw [LocallyConstant.zero_apply, hc, map_prod, Finset.prod_apply]
  refine Finset.prod_eq_zero hξ ?_
  rw [← hc, LocallyConstant.sub_apply, LocallyConstant.one_apply, LocallyConstant.coe_charFn,
    Set.indicator_of_mem hz, Pi.one_apply, sub_self]

/-- **Minimality and compactness**: finitely many translates `ξV` of a nonempty open set cover `Z`. -/
theorem exists_finset_smul_cover [CompactSpace Z] [MulAction.IsMinimal Λ Z] {V : Set Z}
    (hV : IsOpen V) (hne : V.Nonempty) : ∃ s : Finset Λ, ∀ z : Z, ∃ ξ ∈ s, z ∈ ξ • V := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun ξ : Λ => ξ • V)
    (fun ξ => hV.smul ξ) (hV.iUnion_smul Λ hne).ge
  exact ⟨s, fun z => by simpa using hs (Set.mem_univ z)⟩

variable (hcov : IsCovariantPair coeff u)
include hcov

/-- `u_ξ e_V u_ξ⁻¹ = e_{ξV}`. -/
theorem unit_mul_charFn_mul_inv (ξ : Λ) {V : Set Z} (hV : IsClopen V) :
    (u ξ : R) * coeff (LocallyConstant.charFn (ZMod 2) hV) * (((u ξ)⁻¹ : Rˣ) : R) =
      coeff (LocallyConstant.charFn (ZMod 2) (isClopen_smul ξ hV)) := by
  rw [hcov.covariance ξ hV, mul_assoc, Units.mul_inv, mul_one]

/-- **`1 ∈ J`**: the level ideal containing `e_V` contains every `e_{ξV}`, and a finite cover gives
`1 = 1 - ∏ᵢ(1 - e_{ξᵢV})`. -/
theorem one_mem_levelIdeal_of_smul_cover {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 3 ≤ Fintype.card ι) {V : Set Z} (hV : IsClopen V) (s : Finset Λ)
    (hs : ∀ z : Z, ∃ ξ ∈ s, z ∈ ξ • V) (K : Subgroup (elementaryGroup ι R)) [K.Normal]
    (hmem : coeff (LocallyConstant.charFn (ZMod 2) hV) ∈ levelIdeal hcard K) :
    (1 : R) ∈ levelIdeal hcard K := by
  have htrans : ∀ ξ ∈ s,
      coeff (LocallyConstant.charFn (ZMod 2) (isClopen_smul ξ hV)) ∈ levelIdeal hcard K :=
    fun ξ _ => by
      rw [← unit_mul_charFn_mul_inv hcov ξ hV]
      exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hmem)
  have h := one_sub_map_prod_one_sub_mem coeff (levelIdeal hcard K) s _ htrans
  rwa [prod_one_sub_charFn_smul_eq_zero hV s hs, map_zero, sub_zero] at h

variable [DecidableEq Λ]

omit [DecidableEq Λ] in
/-- **The `ε`-span lies in the range of `ψ`.** -/
theorem mem_range_epsilonHom_of_mem_epsilonSpan [DecidableEq Λ] {B : Finset Λ} {V : Set Z}
    (hdisj : TranslatesDisjoint B V) (hV : IsClopen V) {x : R} (hx : x ∈ epsilonSpan coeff u B hV) :
    ∃ M, epsilonHom hcov hdisj hV M = x := by
  have hle : epsilonSpan coeff u B hV ≤ AddMonoidHom.range (epsilonAddHom coeff u B hV) := by
    unfold epsilonSpan
    refine (AddSubgroup.closure_le (K := _)).2 ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact AddMonoidHom.mem_range.2
      ⟨Matrix.single ⟨a, ha⟩ ⟨b, hb⟩ 1, epsilonHom_single hcov hdisj hV ⟨a, ha⟩ ⟨b, hb⟩⟩
  obtain ⟨M, hM⟩ := AddMonoidHom.mem_range.1 (hle hx)
  exact ⟨M, hM⟩

omit [DecidableEq Λ] in
/-- **`k ∈ H_V`**: a unit whose deviations `k - I` and `k⁻¹ - I` have entries in `A_V` is
`(1 - e) I + y` for a unit `y` of `M_ι(A_V)`. -/
theorem exists_copyGL_eq [DecidableEq Λ] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Finset Λ}
    {V : Set Z} (hdisj : TranslatesDisjoint B V) (hV : IsClopen V) (hne : V.Nonempty)
    (g : (Matrix ι ι R)ˣ)
    (hg : ∀ p q, ((g : Matrix ι ι R) - 1) p q ∈ epsilonSpan coeff u B hV)
    (hginv : ∀ p q, (((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1) p q ∈ epsilonSpan coeff u B hV) :
    ∃ x, copyGL hcov ι hdisj hV x = g := by
  obtain ⟨h, hh⟩ := exists_cornerUnitHom_eq (epsilonHom hcov hdisj hV)
    (epsilonHom_injective hcov hdisj hV hne) g
    (fun p q => mem_range_epsilonHom_of_mem_epsilonSpan hcov hdisj hV (hg p q))
    (fun p q => mem_range_epsilonHom_of_mem_epsilonSpan hcov hdisj hV (hginv p q))
  refine ⟨(blockFlatEquiv ι B).symm h, ?_⟩
  rw [copyGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hh]

omit [DecidableEq Λ] in
/-- **`K = G`** from the commutator witness and the finite covering property of nonempty clopen sets. -/
theorem eq_top_of_generalCommutatorWitness {n : ℕ} (hn : 3 ≤ n)
    (hw : GeneralCommutatorWitness coeff u n)
    (hcover : ∀ V : Set Z, IsClopen V → V.Nonempty → ∃ s : Finset Λ, ∀ z : Z, ∃ ξ ∈ s, z ∈ ξ • V)
    (K : Subgroup (elementaryGroup (Fin n) R)) (hK : K.Normal) (hne : K ≠ ⊥) : K = ⊤ := by
  classical
  haveI := hK
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hcard : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  obtain ⟨V, hV, B, g, hVne, hB1, hdisj, hgK, hg1, hent⟩ := hw K hK hne
  obtain ⟨x, hx⟩ := exists_copyGL_eq hcov hdisj hV hVne (g : (Matrix (Fin n) (Fin n) R)ˣ)
    (fun p q => (hent p q).1) (fun p q => (hent p q).2)
  let H : (Matrix (Fin n × B) (Fin n × B) (ZMod 2))ˣ →* elementaryGroup (Fin n) R :=
    (copyGL hcov (Fin n) hdisj hV).codRestrict _ (copyGL_mem_elementaryGroup hcov hdisj hV)
  have hHx : H x = g := Subtype.ext hx
  have hcardB : 1 ≤ Fintype.card B := by
    rw [Fintype.card_coe]
    exact Finset.card_pos.2 ⟨1, hB1⟩
  have hcardd : 3 ≤ Fintype.card (Fin n × B) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    calc 3 ≤ n := hn
      _ ≤ n * Fintype.card B := by nlinarith [hcardB]
  haveI := FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo (Fin n × B) hcardd
  have hxK : x ∈ K.comap H := by
    rw [Subgroup.mem_comap, hHx]
    exact hgK
  have hx1 : x ≠ 1 := fun h => hg1 (by rw [← hHx, h, map_one])
  have htop : K.comap H = ⊤ :=
    (hK.comap H).eq_bot_or_eq_top.resolve_left fun hb => hx1 (Subgroup.mem_bot.1 (hb ▸ hxK))
  have hroot : ∀ (p q : Fin n) (hpq : p ≠ q),
      elGen p q hpq (coeff (LocallyConstant.charFn (ZMod 2) hV)) ∈ K := by
    intro p q hpq
    have hne' : ((p, ⟨1, hB1⟩) : Fin n × B) ≠ (q, ⟨1, hB1⟩) := by simp [hpq]
    have hmem : elementaryUnit _ _ hne' (1 : ZMod 2) ∈ K.comap H := by
      rw [htop]
      exact Subgroup.mem_top _
    have hH : H (elementaryUnit _ _ hne' (1 : ZMod 2)) =
        elGen p q hpq (coeff (LocallyConstant.charFn (ZMod 2) hV)) := by
      apply Subtype.ext
      change copyGL hcov (Fin n) hdisj hV (elementaryUnit _ _ hne' (1 : ZMod 2)) =
        elementaryUnit p q hpq _
      rw [copyGL_transvection hcov hdisj hV hpq _ _ hne']
      exact congrArg (elementaryUnit p q hpq) (epsilon_one_one (coeff := coeff) (u := u) hV)
    rw [← hH]
    exact hmem
  have hmemJ : coeff (LocallyConstant.charFn (ZMod 2) hV) ∈ levelIdeal hcard K :=
    (mem_levelIdeal hcard K _).2 hroot
  obtain ⟨s, hs⟩ := hcover V hV hVne
  have h1 := one_mem_levelIdeal_of_smul_cover hcov hcard hV s hs K hmemJ
  rw [Subgroup.eq_top_iff']
  intro y
  have hy := elementaryGroup_hom_eq_one_of_gens (QuotientGroup.mk' K)
    (fun l k hlk d => by
      have hd := TwoSidedIdeal.mul_mem_left _ d 1 h1
      rw [mul_one] at hd
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (mem_levelIdeal hcard K d).mp hd l k hlk) y
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy

omit [DecidableEq Λ] in
/-- **`EL_n(R)` is simple** for `n ≥ 3`, over a nonempty compact space with a minimal action, from the
commutator witness. -/
theorem isSimpleGroup_of_generalCommutatorWitness [CompactSpace Z] [MulAction.IsMinimal Λ Z]
    [Nonempty Z] {n : ℕ} (hn : 3 ≤ n) (hw : GeneralCommutatorWitness coeff u n) :
    IsSimpleGroup ↥(elementaryGroup (Fin n) R) := by
  have h10 : (1 : R) ≠ 0 := by
    intro h
    have h1 : (1 : LocallyConstant Z (ZMod 2)) = 0 :=
      hcov.injective (by rw [map_one, map_zero, h])
    have h2 := LocallyConstant.congr_fun h1 (Classical.arbitrary Z)
    simp at h2
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hne1 : elGen (R := R) _ _ h01 1 ≠ 1 := by
    intro h
    have h' : elementaryUnit (R := R) _ _ h01 1 = elementaryUnit _ _ h01 0 := by
      rw [elementaryUnit_zero]
      exact congrArg Subtype.val h
    exact h10 (elementaryUnit_injective _ _ h01 h')
  haveI : Nontrivial ↥(elementaryGroup (Fin n) R) := nontrivial_of_ne _ _ hne1
  refine ⟨fun K hK => ?_⟩
  by_cases hb : K = ⊥
  · exact Or.inl hb
  · exact Or.inr (eq_top_of_generalCommutatorWitness hcov hn hw
      (fun _ hV hne' => exists_finset_smul_cover hV.isOpen hne') K hK hb)

/-- **Printed simplicity for group actions** (`thm:general`, simplicity clause), from the commutator
witness produced by the first half of the proof. -/
def PrintedGeneralSimplicityFromWitness : Prop :=
  ∀ (Λ Z R : Type) [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]
    [CompactSpace Z] [MulAction.IsMinimal Λ Z] [Nonempty Z] [Ring R]
    (coeff : LocallyConstant Z (ZMod 2) →+* R) (u : Λ →* Rˣ), IsCovariantPair coeff u →
    ∀ n : ℕ, 3 ≤ n → GeneralCommutatorWitness coeff u n →
      IsSimpleGroup ↥(elementaryGroup (Fin n) R)

omit hcov [DecidableEq Λ] in
theorem printedGeneralSimplicityFromWitness : PrintedGeneralSimplicityFromWitness :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hcov _ hn hw => isSimpleGroup_of_generalCommutatorWitness hcov hn hw

#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.exists_copyGL_eq
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.eq_top_of_generalCommutatorWitness
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.isSimpleGroup_of_generalCommutatorWitness
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.printedGeneralSimplicityFromWitness

end General
end SimpleKazhdanSofic
end GroupApproximation
