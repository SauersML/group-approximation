import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSimplicityNormalSubgroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.TowerCopyGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Steps 2–3 of the simplicity proof: the commutator lies in `H_V ⊆ K`, and `e_{ξV} ∈ J`

`simple_kazhdan_sofic_group.tex` (HEAD), subsection "Simplicity".

Step 2, tex l.292–294:

> Then $y=1_VI_3+(x-I_3)$ and $y'=1_VI_3+(x^{-1}-I_3)$ satisfy
> $yy'=y'y=1_VI_3$, so $x=(1-1_V)I_3+y\in H_V$.

Step 2, tex l.294–296:

> As $K\cap H_V$ is a nontrivial normal subgroup of
> $H_V\cong\GL_d(\F_2)=\PSL_d(\F_2)$, which is simple as $d\ge3$, we get
> $H_V\subseteq K$, and $e_{pq}(e_V)\in K$ for all $p\ne q$.

Step 3, tex l.302–303 (with `J = {r : e_pq(r) ∈ K for all p ≠ q}`, l.299):

> It contains $e_V$, so it contains every $e_{\xi V}=u_\xi e_Vu_\xi^{-1}$.

The ring `R` carries a covariant pair (`IsCovariantPair coeff u`), `ε_ab = e_{aV} u_{ab⁻¹}` is
`SimpleKazhdanSofic.epsilon`, and `A_V` is `epsilonSpan coeff u B hV`. The translates `aV`,
`a ∈ B`, are disjoint (`TranslatesDisjoint B V`), which holds for a small `V`; see
`Audit1.manuscriptSentence_epsilonProductRule`. `H_V` is the image of `General.copyGL`, i.e.
`y ↦ (1 - 1_V) I + y` on `GL_ι(A_V) ≅ GL_{ι × B}(F_2)`. `towerCopyEL` is the same map with values in
`EL_ι(R)`. The matrix size is an arbitrary finite `ι` with `|ι| ≥ 3`; the printed `3` is `ι = Fin 3`,
and `d = |ι × B|`.

Proof routes.
* `manuscriptSentence_cornerUnitInCopy`:
  * `1_V = ∑_a ε_aa = ψ(1)` is a two-sided unit for `A_V`, since `ψ` is multiplicative and onto
    `A_V`. So `(1_V I) M = M = M (1_V I)` for matrices over `A_V`, and `(1_V I)² = 1_V I`.
  * With `X = x - I` and `Y = x⁻¹ - I`, the identity `x x⁻¹ = I` gives `XY = -X - Y`. Hence
    `(1_V I + X)(1_V I + Y) = 1_V I + X + Y + XY = 1_V I`, and symmetrically.
  * `x = (1 - 1_V) I + y` is additive bookkeeping, and `x ∈ H_V` is `General.exists_copyGL_eq`.
* `manuscriptSentence_copyInsideNormalSubgroup`:
  * `d = |ι|·|B| ≥ 3` as `e ∈ B`.
  * `GL_d(F_2)` is simple (`FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo`), has determinant
    one throughout and trivial centre (`GL = SL = PSL`), and `towerCopyEL` is injective.
  * The preimage of `K` is normal and contains the nontrivial preimage of `x`, so it is everything.
  * The image of the transvection at `((p,e),(q,e))` is `e_pq(ε_ee) = e_pq(e_V)`.
* `manuscriptSentence_translatesInLevelIdeal`:
  * `J` is `Pestov91.SimpleModCentre.levelIdeal`, a two-sided ideal with exactly this membership.
  * `u_ξ e_V u_ξ⁻¹ = e_{ξV}` is covariance, and two-sided ideals absorb products.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Audit1

open Pointwise ChainRadical Pestov91.SimpleModCentre

variable {Λ Z R : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]
  [Ring R] {coeff : LocallyConstant Z (ZMod 2) →+* R} {u : Λ →* Rˣ}

/-- **tex l.292–294.** Suppose the entries of `x - I` and `x⁻¹ - I` lie in `A_V`, for a nonempty `V`
with disjoint translates. Then, with `1_V = ∑_a ε_aa`:
* `y = 1_V I + (x - I)` and `y' = 1_V I + (x⁻¹ - I)` lie in `M_ι(A_V)`;
* `y y' = y' y = 1_V I`;
* `x = (1 - 1_V) I + y`;
* `x` lies in the image `H_V` of `y ↦ (1 - 1_V) I + y` on `GL_{ι×B}(F_2) ≅ GL_ι(A_V)`. -/
theorem manuscriptSentence_cornerUnitInCopy [DecidableEq Λ] (hcov : IsCovariantPair coeff u)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Finset Λ} {V : Set Z} (hV : IsClopen V)
    (hdisj : TranslatesDisjoint B V) (hne : V.Nonempty) (x : (Matrix ι ι R)ˣ)
    (hx : ∀ p q, ((x : Matrix ι ι R) - 1) p q ∈ epsilonSpan coeff u B hV)
    (hxinv : ∀ p q, (((x⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1) p q ∈
      epsilonSpan coeff u B hV) :
    (∀ p q, (Matrix.scalar ι (∑ a : B, epsilon coeff u hV a a) + ((x : Matrix ι ι R) - 1)) p q ∈
      epsilonSpan coeff u B hV) ∧
    (∀ p q, (Matrix.scalar ι (∑ a : B, epsilon coeff u hV a a) +
        (((x⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1)) p q ∈ epsilonSpan coeff u B hV) ∧
    (Matrix.scalar ι (∑ a : B, epsilon coeff u hV a a) + ((x : Matrix ι ι R) - 1)) *
        (Matrix.scalar ι (∑ a : B, epsilon coeff u hV a a) +
          (((x⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1)) =
      Matrix.scalar ι (∑ a : B, epsilon coeff u hV a a) ∧
    (Matrix.scalar ι (∑ a : B, epsilon coeff u hV a a) +
          (((x⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1)) *
        (Matrix.scalar ι (∑ a : B, epsilon coeff u hV a a) + ((x : Matrix ι ι R) - 1)) =
      Matrix.scalar ι (∑ a : B, epsilon coeff u hV a a) ∧
    (x : Matrix ι ι R) = Matrix.scalar ι (1 - ∑ a : B, epsilon coeff u hV a a) +
      (Matrix.scalar ι (∑ a : B, epsilon coeff u hV a a) + ((x : Matrix ι ι R) - 1)) ∧
    ∃ z : (Matrix (ι × B) (ι × B) (ZMod 2))ˣ, General.copyGL hcov ι hdisj hV z = x := by
  have hgen : ∀ a b : B, epsilon coeff u hV a b ∈ epsilonSpan coeff u B hV :=
    fun a b => AddSubgroup.subset_closure ⟨a, a.2, b, b.2, rfl⟩
  have hspan : ∀ y : R, y ∈ epsilonSpan coeff u B hV ↔
      ∃ M, General.epsilonHom hcov hdisj hV M = y := by
    intro y
    refine ⟨fun hy => General.mem_range_epsilonHom_of_mem_epsilonSpan hcov hdisj hV hy, ?_⟩
    rintro ⟨M, rfl⟩
    rw [General.epsilonHom_apply]
    exact _root_.sum_mem fun a _ => _root_.sum_mem fun b _ => _root_.nsmul_mem (hgen a b) _
  have hone : General.epsilonHom hcov hdisj hV 1 = ∑ a : B, epsilon coeff u hV a a := by
    rw [General.epsilonHom_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hoff : ∀ b : B, b ≠ a →
        ((1 : Matrix B B (ZMod 2)) a b).val • epsilon coeff u hV a b = 0 := by
      intro b hb
      rw [Matrix.one_apply_ne hb.symm, ZMod.val_zero, zero_nsmul]
    rw [Fintype.sum_eq_single a hoff, Matrix.one_apply_eq, show (1 : ZMod 2).val = 1 from rfl,
      one_nsmul]
  obtain ⟨e, he⟩ : ∃ e : R, e = ∑ a : B, epsilon coeff u hV a a := ⟨_, rfl⟩
  rw [← he] at hone ⊢
  have hmem1 : e ∈ epsilonSpan coeff u B hV := by
    rw [← hone]
    exact (hspan _).2 ⟨1, rfl⟩
  -- `1_V` is a two-sided unit of `A_V`
  have hunit : ∀ y ∈ epsilonSpan coeff u B hV, e * y = y ∧ y * e = y := by
    intro y hy
    obtain ⟨M, rfl⟩ := (hspan y).1 hy
    refine ⟨?_, ?_⟩
    · rw [← hone, ← map_mul (General.epsilonHom hcov hdisj hV), one_mul]
    · rw [← hone, ← map_mul (General.epsilonHom hcov hdisj hV), mul_one]
  have hSM : ∀ M : Matrix ι ι R, (∀ p q, M p q ∈ epsilonSpan coeff u B hV) →
      Matrix.scalar ι e * M = M ∧ M * Matrix.scalar ι e = M := by
    intro M hM
    refine ⟨?_, ?_⟩
    · ext p q
      rw [Matrix.scalar_apply, Matrix.diagonal_mul]
      exact (hunit _ (hM p q)).1
    · ext p q
      rw [Matrix.scalar_apply, Matrix.mul_diagonal]
      exact (hunit _ (hM p q)).2
  have hSS : Matrix.scalar ι e * Matrix.scalar ι e = Matrix.scalar ι e := by
    rw [← map_mul (Matrix.scalar ι) e e, (hunit e hmem1).1]
  have hdiag : ∀ p q, Matrix.scalar ι e p q ∈ epsilonSpan coeff u B hV := by
    intro p q
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact hmem1
    · exact AddSubgroup.zero_mem _
  -- `x x⁻¹ = I` and `x⁻¹ x = I` in terms of `X = x - I` and `Y = x⁻¹ - I`
  have hxx : ((x : Matrix ι ι R) - 1) * (((x⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1) =
      -((x : Matrix ι ι R) - 1) - (((x⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, Units.mul_inv]
    abel
  have hxx' : (((x⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1) * ((x : Matrix ι ι R) - 1) =
      -(((x⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1) - ((x : Matrix ι ι R) - 1) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, Units.inv_mul]
    abel
  have hprod : ∀ X Y : Matrix ι ι R, (∀ p q, X p q ∈ epsilonSpan coeff u B hV) →
      (∀ p q, Y p q ∈ epsilonSpan coeff u B hV) → X * Y = -X - Y →
        (Matrix.scalar ι e + X) * (Matrix.scalar ι e + Y) = Matrix.scalar ι e := by
    intro X Y hXs hYs hXY
    rw [add_mul, mul_add, mul_add, hSS, (hSM Y hYs).1, (hSM X hXs).2, hXY]
    abel
  refine ⟨fun p q => ?_, fun p q => ?_, hprod _ _ hx hxinv hxx, hprod _ _ hxinv hx hxx', ?_,
    General.exists_copyGL_eq hcov hdisj hV hne x hx hxinv⟩
  · rw [Matrix.add_apply]
    exact _root_.add_mem (hdiag p q) (hx p q)
  · rw [Matrix.add_apply]
    exact _root_.add_mem (hdiag p q) (hxinv p q)
  · rw [map_sub, map_one]
    abel

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit1.manuscriptSentence_cornerUnitInCopy

/-- The copy `H_V` of `GL_{ι × B}(F_2)`, `y ↦ (1 - 1_V) I + y`, with values in `EL_ι(R)`
(`General.copyGL_mem_elementaryGroup`). -/
noncomputable def towerCopyEL [DecidableEq Λ] (hcov : IsCovariantPair coeff u) (ι : Type*)
    [Fintype ι] [DecidableEq ι] [Nontrivial ι] {B : Finset Λ} {V : Set Z}
    (hdisj : TranslatesDisjoint B V) (hV : IsClopen V) :
    (Matrix (ι × B) (ι × B) (ZMod 2))ˣ →* elementaryGroup ι R :=
  (General.copyGL hcov ι hdisj hV).codRestrict _ (General.copyGL_mem_elementaryGroup hcov hdisj hV)

/-- **tex l.294–296.** Let `K ⊴ EL_ι(R)` with `|ι| ≥ 3`, `e ∈ B`, and `V` nonempty with disjoint
translates. Suppose some `k ∈ K ∖ {1}` lies in `H_V`, i.e. `k = (1 - 1_V) I + y` for
`y ∈ GL_{ι×B}(F_2)`. Then:
* `d = |ι × B| ≥ 3`, and `GL_d(F_2)` is simple;
* `GL_d(F_2) = PSL_d(F_2)`: every determinant is `1` and the centre is trivial;
* `H_V ≅ GL_d(F_2)`, since the copy is injective;
* `K ∩ H_V` (the preimage of `K`) is a nontrivial normal subgroup, hence everything, so `H_V ⊆ K`;
* `e_pq(e_V) ∈ K` for all `p ≠ q`. -/
theorem manuscriptSentence_copyInsideNormalSubgroup [DecidableEq Λ]
    (hcov : IsCovariantPair coeff u) {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (hcard : 3 ≤ Fintype.card ι) {B : Finset Λ} {V : Set Z} (hV : IsClopen V)
    (hdisj : TranslatesDisjoint B V) (hne : V.Nonempty) (hB1 : (1 : Λ) ∈ B)
    (K : Subgroup (elementaryGroup ι R)) [K.Normal] (k : elementaryGroup ι R) (hkK : k ∈ K)
    (hk1 : k ≠ 1) (y : (Matrix (ι × B) (ι × B) (ZMod 2))ˣ)
    (hy : General.copyGL hcov ι hdisj hV y = (k : (Matrix ι ι R)ˣ)) :
    3 ≤ Fintype.card (ι × B) ∧
    IsSimpleGroup (Matrix (ι × B) (ι × B) (ZMod 2))ˣ ∧
    (∀ z : (Matrix (ι × B) (ι × B) (ZMod 2))ˣ, (z : Matrix (ι × B) (ι × B) (ZMod 2)).det = 1) ∧
    Subgroup.center (Matrix (ι × B) (ι × B) (ZMod 2))ˣ = ⊥ ∧
    Function.Injective (towerCopyEL hcov ι hdisj hV) ∧
    (K.comap (towerCopyEL hcov ι hdisj hV)).Normal ∧
    K.comap (towerCopyEL hcov ι hdisj hV) ≠ ⊥ ∧
    K.comap (towerCopyEL hcov ι hdisj hV) = ⊤ ∧
    ∀ (p q : ι) (hpq : p ≠ q), elGen p q hpq (coeff (LocallyConstant.charFn (ZMod 2) hV)) ∈ K := by
  have hHy : towerCopyEL hcov ι hdisj hV y = k := Subtype.ext hy
  have hcardB : 1 ≤ Fintype.card B := by
    rw [Fintype.card_coe]
    exact Finset.card_pos.2 ⟨1, hB1⟩
  have hcardd : 3 ≤ Fintype.card (ι × B) := by
    rw [Fintype.card_prod]
    calc 3 ≤ Fintype.card ι := hcard
      _ ≤ Fintype.card ι * Fintype.card B := Nat.le_mul_of_pos_right _ hcardB
  haveI := FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo (ι × B) hcardd
  have hinj : Function.Injective (towerCopyEL hcov ι hdisj hV) := by
    intro a b hab
    exact General.copyGL_injective hcov hdisj hV hne (congrArg Subtype.val hab)
  have hyK : y ∈ K.comap (towerCopyEL hcov ι hdisj hV) := by
    rw [Subgroup.mem_comap, hHy]
    exact hkK
  have hy1 : y ≠ 1 := fun h => hk1 (by rw [← hHy, h, map_one])
  have hnormal : (K.comap (towerCopyEL hcov ι hdisj hV)).Normal :=
    (inferInstance : K.Normal).comap _
  have hbot : K.comap (towerCopyEL hcov ι hdisj hV) ≠ ⊥ :=
    fun hb => hy1 (by rw [hb] at hyK; exact Subgroup.mem_bot.1 hyK)
  have htop : K.comap (towerCopyEL hcov ι hdisj hV) = ⊤ :=
    hnormal.eq_bot_or_eq_top.resolve_left hbot
  have hroot : ∀ (p q : ι) (hpq : p ≠ q),
      elGen p q hpq (coeff (LocallyConstant.charFn (ZMod 2) hV)) ∈ K := by
    intro p q hpq
    have hne' : ((p, ⟨1, hB1⟩) : ι × B) ≠ (q, ⟨1, hB1⟩) := by simp [hpq]
    have hmem : elementaryUnit _ _ hne' (1 : ZMod 2) ∈ K.comap (towerCopyEL hcov ι hdisj hV) := by
      rw [htop]
      exact Subgroup.mem_top _
    have hH : towerCopyEL hcov ι hdisj hV (elementaryUnit _ _ hne' (1 : ZMod 2)) =
        elGen p q hpq (coeff (LocallyConstant.charFn (ZMod 2) hV)) := by
      apply Subtype.ext
      change General.copyGL hcov ι hdisj hV (elementaryUnit _ _ hne' (1 : ZMod 2)) =
        elementaryUnit p q hpq _
      rw [General.copyGL_transvection hcov hdisj hV hpq _ _ hne']
      exact congrArg (elementaryUnit p q hpq) (General.epsilon_one_one (coeff := coeff) (u := u) hV)
    rw [← hH]
    exact hmem
  exact ⟨hcardd, inferInstance, fun z => det_units_matrix_zmodTwo z,
    center_units_matrix_zmodTwo_eq_bot (ι × B) hcardd, hinj, hnormal, hbot, htop, hroot⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit1.manuscriptSentence_copyInsideNormalSubgroup

/-- **tex l.302–303.** Let `J = {r ∈ R : e_pq(r) ∈ K for all p ≠ q}` (`levelIdeal`, a two-sided
ideal). If `J` contains `e_V`, then for every `ξ`: `u_ξ e_V u_ξ⁻¹ = e_{ξV}`, `e_{ξV} ∈ J`, and
`e_pq(e_{ξV}) ∈ K` for all `p ≠ q`. -/
theorem manuscriptSentence_translatesInLevelIdeal (hcov : IsCovariantPair coeff u)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hcard : 3 ≤ Fintype.card ι)
    (K : Subgroup (elementaryGroup ι R)) [K.Normal] {V : Set Z} (hV : IsClopen V)
    (hroot : ∀ (p q : ι) (hpq : p ≠ q),
      elGen p q hpq (coeff (LocallyConstant.charFn (ZMod 2) hV)) ∈ K) :
    (∀ r : R, r ∈ levelIdeal hcard K ↔ ∀ (p q : ι) (hpq : p ≠ q), elGen p q hpq r ∈ K) ∧
    coeff (LocallyConstant.charFn (ZMod 2) hV) ∈ levelIdeal hcard K ∧
    ∀ ξ : Λ,
      (u ξ : R) * coeff (LocallyConstant.charFn (ZMod 2) hV) * (((u ξ)⁻¹ : Rˣ) : R) =
          coeff (LocallyConstant.charFn (ZMod 2) (isClopen_smul ξ hV)) ∧
        coeff (LocallyConstant.charFn (ZMod 2) (isClopen_smul ξ hV)) ∈ levelIdeal hcard K ∧
        ∀ (p q : ι) (hpq : p ≠ q),
          elGen p q hpq (coeff (LocallyConstant.charFn (ZMod 2) (isClopen_smul ξ hV))) ∈ K := by
  have hJ : coeff (LocallyConstant.charFn (ZMod 2) hV) ∈ levelIdeal hcard K :=
    (mem_levelIdeal hcard K _).2 hroot
  refine ⟨fun r => mem_levelIdeal hcard K r, hJ, fun ξ => ?_⟩
  have htrans : coeff (LocallyConstant.charFn (ZMod 2) (isClopen_smul ξ hV)) ∈
      levelIdeal hcard K := by
    rw [← General.unit_mul_charFn_mul_inv hcov ξ hV]
    exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hJ)
  exact ⟨General.unit_mul_charFn_mul_inv hcov ξ hV, htrans, (mem_levelIdeal hcard K _).1 htrans⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit1.manuscriptSentence_translatesInLevelIdeal

end Audit1
end SimpleKazhdanSofic
end GroupApproximation
