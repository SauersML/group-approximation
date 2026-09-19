import GroupApproximation.Manuscript.SimpleKazhdanSofic.TowerCopy
import GroupApproximation.Leavitt.CornerUnitHom
import GroupApproximation.Algebra.FinitaryLinearBinarySimple
import Mathlib.Data.Matrix.Composition

/-!
# The copy `H` of `GL_d(F_2)` on the tower over `V`

`simple_kazhdan_sofic_group.tex` (origin/main tip), subsection "Simplicity":

> Index the coordinates of $\F_2^d$ by pairs $(p,a)$ with $1\le p\le3$ and $|a|\le w$. Then
> $\psi(E_{(p,a),(q,b)})=\epsilon_{ab}E_{pq}$ defines an injective multiplicative linear map
> $\psi\colon M_d(\F_2)\to M_3(R)$, and $M\mapsto I_3-\psi(I_d)+\psi(M)$ embeds $\GL_d(\F_2)$ in
> $\GL_3(R)$. Its image $H$ lies in $G$. Indeed, transvections generate $\GL_d(\F_2)$. The
> transvection between $(p,a)$ and $(q,b)$ maps to $e_{pq}(\epsilon_{ab})$ if $p\ne q$. If $p=q$,
> it is the commutator of the transvections between $(p,a)$ and $(p',a)$ and between $(p',a)$ and
> $(p,b)$, where $p'\ne p$.
> … $H\cong\GL_d(\F_2)=\PSL_d(\F_2)$, which is simple as $d\ge3$.

The index set `ι` of the outer matrices is arbitrary (printed `ι = {1,2,3}`; `thm:main` covers every
`EL_n`, `n ≥ 3`), and `d = #ι · (2m+1)`.

* `flatEquiv ι m : GL_{ι × (2m+1)}(F_2) ≃* GL_ι(M_{2m+1}(F_2))`, block flattening;
* `towerCopy ι hlev hWU hW`: `M ↦ I - ψ(I_d) + ψ(M)` on units, the corner map of `towerHom`;
* `towerCopy_transvection`: the transvection between `(p,a)` and `(q,b)`, `p ≠ q`, goes to
  `e_{pq}(ε_{ab})`;
* `towerCopy_mem_elementaryGroup`: `H ≤ EL_ι(R_X)`, through transvections and, for `p = q`, the
  printed commutator;
* `towerCopy_injective` for nonempty `W`;
* `det_units_matrix_zmodTwo`, `center_units_matrix_zmodTwo_eq_bot`: `GL_d(F_2) = SL_d(F_2)` and its
  centre is trivial for `d ≥ 3`, so `GL_d(F_2) = PSL_d(F_2)`; it is simple
  (`FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open ClopenCrossedProduct ChainRadical

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {m : ℕ} {U W : Set X}

/-- Flattening block coordinates: `GL_{ι × (2m+1)}(F_2) ≃* GL_ι(M_{2m+1}(F_2))`. -/
noncomputable def flatEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) :
    (Matrix (ι × Fin (2 * m + 1)) (ι × Fin (2 * m + 1)) (ZMod 2))ˣ ≃*
      (Matrix ι ι (Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) (ZMod 2)))ˣ :=
  Units.mapEquiv (Matrix.compRingEquiv ι (Fin (2 * m + 1)) (ZMod 2)).symm.toMulEquiv

/-- **The copy `H`** of `GL_{ι × (2m+1)}(F_2)` acting on the tower over `W`:
`M ↦ I - ψ(I_d) + ψ(M)`. -/
noncomputable def towerCopy (ι : Type*) [Fintype ι] [DecidableEq ι] (hlev : LevelsDisjoint T m U)
    (hWU : W ⊆ U) (hW : IsClopen W) :
    (Matrix (ι × Fin (2 * m + 1)) (ι × Fin (2 * m + 1)) (ZMod 2))ˣ →*
      (Matrix ι ι (ClopenCrossedProduct T (ZMod 2)))ˣ :=
  (cornerUnitHom (ι := ι) (towerHom hlev hWU hW)).comp (flatEquiv ι m).toMonoidHom

theorem flatEquiv_elementaryUnit {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ι} (hpq : p ≠ q)
    (a b : Fin (2 * m + 1)) (c : ZMod 2) (h : (p, a) ≠ (q, b)) :
    flatEquiv ι m (elementaryUnit (p, a) (q, b) h c) =
      elementaryUnit p q hpq (Matrix.single a b c) := by
  apply Units.ext
  change (Matrix.compRingEquiv ι (Fin (2 * m + 1)) (ZMod 2)).symm
      (1 + Matrix.single (p, a) (q, b) c) = 1 + Matrix.single p q (Matrix.single a b c)
  rw [map_add, map_one, ← Matrix.comp_single_single, Matrix.compRingEquiv_symm_apply,
    Equiv.symm_apply_apply]

theorem towerCopy_elementaryUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U) (hW : IsClopen W) {p q : ι} (hpq : p ≠ q)
    (a b : Fin (2 * m + 1)) (c : ZMod 2) (h : (p, a) ≠ (q, b)) :
    towerCopy ι hlev hWU hW (elementaryUnit (p, a) (q, b) h c) =
      elementaryUnit p q hpq (towerHom hlev hWU hW (Matrix.single a b c)) := by
  rw [towerCopy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    flatEquiv_elementaryUnit hpq a b c h, cornerUnitHom_elementaryUnit]

/-- **The transvection between `(p,a)` and `(q,b)` maps to `e_{pq}(ε_{ab})`** if `p ≠ q`. -/
theorem towerCopy_transvection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U) (hW : IsClopen W) {p q : ι} (hpq : p ≠ q)
    (a b : Fin (2 * m + 1)) (h : (p, a) ≠ (q, b)) :
    towerCopy ι hlev hWU hW (elementaryUnit (p, a) (q, b) h 1) =
      elementaryUnit p q hpq (towerE T (ZMod 2) m hW a b) := by
  rw [towerCopy_elementaryUnit hlev hWU hW hpq a b 1 h, towerHom_single]

/-- **`H` lies in `G`** (tex, "Its image $H$ lies in $G$"): transvections generate `GL_d(F_2)`; a
transvection with `p ≠ q` maps to a root, and one with `p = q` is a commutator of two such. -/
theorem towerCopy_mem_elementaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U) (hW : IsClopen W)
    (x : (Matrix (ι × Fin (2 * m + 1)) (ι × Fin (2 * m + 1)) (ZMod 2))ˣ) :
    towerCopy ι hlev hWU hW x ∈ elementaryGroup ι (ClopenCrossedProduct T (ZMod 2)) := by
  have hx : x ∈ elementaryGroup (ι × Fin (2 * m + 1)) (ZMod 2) := by
    rw [FinitaryLinear.elementaryGroup_zmodTwo_eq_top]
    exact Subgroup.mem_top x
  have hroot : ∀ {p q : ι} (hpq : p ≠ q) (a b : Fin (2 * m + 1)) (c : ZMod 2)
      (h : (p, a) ≠ (q, b)), towerCopy ι hlev hWU hW (elementaryUnit (p, a) (q, b) h c) ∈
        elementaryGroup ι (ClopenCrossedProduct T (ZMod 2)) := by
    intro p q hpq a b c h
    rw [towerCopy_elementaryUnit hlev hWU hW hpq a b c h]
    exact elementaryUnit_mem _ _ _ _
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨⟨p, a⟩, ⟨q, b⟩, hne, c, rfl⟩ := hy
    by_cases hpq : p = q
    · subst hpq
      obtain ⟨p', hp'⟩ := exists_ne p
      have h1 : ((p, a) : ι × Fin (2 * m + 1)) ≠ (p', a) := by simp [hp'.symm]
      have h2 : ((p', a) : ι × Fin (2 * m + 1)) ≠ (p, b) := by simp [hp']
      have hcomm := elementaryUnit_commutator (R := ZMod 2) ((p, a) : ι × Fin (2 * m + 1))
        (p', a) (p, b) h1 h2 hne c 1
      rw [mul_one] at hcomm
      rw [← hcomm, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (hroot hp'.symm a a c h1) (hroot hp' a b 1 h2))
        (Subgroup.inv_mem _ (hroot hp'.symm a a c h1))) (Subgroup.inv_mem _ (hroot hp' a b 1 h2))
    · exact hroot hpq a b c hne
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul y z _ _ hy hz => rw [map_mul]; exact Subgroup.mul_mem _ hy hz
  | inv y _ hy => rw [map_inv]; exact Subgroup.inv_mem _ hy

/-- **The copy is injective** for nonempty `W` (printed "embeds $\GL_d(\F_2)$"). -/
theorem towerCopy_injective {ι : Type*} [Fintype ι] [DecidableEq ι] (hlev : LevelsDisjoint T m U)
    (hWU : W ⊆ U) (hW : IsClopen W) (hne : W.Nonempty) :
    Function.Injective (towerCopy ι hlev hWU hW) := by
  intro x y h
  have h' : cornerUnitHom (ι := ι) (towerHom hlev hWU hW) (flatEquiv ι m x) =
      cornerUnitHom (ι := ι) (towerHom hlev hWU hW) (flatEquiv ι m y) := h
  exact (flatEquiv ι m).injective (cornerUnitHom_injective _ (towerHom_injective hlev hWU hW hne) h')

/-- **`GL_d(F_2) = SL_d(F_2)`**: every invertible matrix over `F_2` has determinant `1`. -/
theorem det_units_matrix_zmodTwo {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (Matrix ι ι (ZMod 2))ˣ) : (u : Matrix ι ι (ZMod 2)).det = 1 := by
  have hdet : (u : Matrix ι ι (ZMod 2)).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse
      (B := ((u⁻¹ : (Matrix ι ι (ZMod 2))ˣ) : Matrix ι ι (ZMod 2))) u.mul_inv
  have h2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact h2 _ hdet

/-- **`GL_d(F_2)` is centerless** for `d ≥ 3`, so `GL_d(F_2) = PSL_d(F_2)`. -/
theorem center_units_matrix_zmodTwo_eq_bot (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hcard : 3 ≤ Fintype.card ι) : Subgroup.center (Matrix ι ι (ZMod 2))ˣ = ⊥ := by
  haveI := FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo ι hcard
  refine (Subgroup.Normal.eq_bot_or_eq_top
    (inferInstance : (Subgroup.center (Matrix ι ι (ZMod 2))ˣ).Normal)).resolve_right fun htop => ?_
  obtain ⟨i, j, hij⟩ : ∃ i j : ι, i ≠ j := Fintype.exists_pair_of_one_lt_card (by omega)
  have hc : elementaryUnit i j hij (1 : ZMod 2) ∈ Subgroup.center (Matrix ι ι (ZMod 2))ˣ := by
    rw [htop]
    exact Subgroup.mem_top _
  have hcomm := Subgroup.mem_center_iff.1 hc (elementaryUnit j i hij.symm 1)
  have hval : ((1 + Matrix.single j i (1 : ZMod 2)) * (1 + Matrix.single i j 1) :
        Matrix ι ι (ZMod 2)) i i =
      ((1 + Matrix.single i j (1 : ZMod 2)) * (1 + Matrix.single j i 1) : Matrix ι ι (ZMod 2)) i i :=
    congrArg (fun u : (Matrix ι ι (ZMod 2))ˣ => (u : Matrix ι ι (ZMod 2)) i i) hcomm
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.single_mul_single_same, Matrix.add_apply,
    Matrix.one_apply_eq, Matrix.single_apply_same, Matrix.single_apply_of_row_ne hij.symm,
    Matrix.single_apply_of_col_ne _ _ hij.symm, add_zero, zero_add] at hval
  revert hval
  decide

#audit_axioms GroupApproximation.SimpleKazhdanSofic.towerCopy_transvection
#audit_axioms GroupApproximation.SimpleKazhdanSofic.towerCopy_mem_elementaryGroup
#audit_axioms GroupApproximation.SimpleKazhdanSofic.towerCopy_injective
#audit_axioms GroupApproximation.SimpleKazhdanSofic.center_units_matrix_zmodTwo_eq_bot

end SimpleKazhdanSofic
end GroupApproximation
