import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimplicityNormalSubgroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.StepanovSimplicity
import GroupApproximation.Manuscript.SimpleKazhdanSofic.RingPartitions
import GroupApproximation.Manuscript.SimpleKazhdanSofic.TowerMatrixUnits
import GroupApproximation.Manuscript.SimpleKazhdanSofic.TowerCopy
import Mathlib.GroupTheory.Commutator.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:main`, proof sketch: the simplicity ingredient, and Figure (b)

`simple_kazhdan_sofic_group.tex`, l.120–124:

> \emph{Simplicity.} A nontrivial normal subgroup contains a nontrivial commutator lying in a copy
> of the finite simple group $\GL_d(\F_2)$ over a clopen tower, a small clopen set with its disjoint
> translates (Figure~\ref{fig:models}(b)). So it contains this group and with it an elementary
> matrix, from which minimality gives every elementary matrix.

and the TikZ scope of Figure (b), l.150–156 (caption l.163–165: "A small clopen set $V$ and
translates $aV$ and $bV$; the matrix units $\epsilon_{ab}=e_{aV}u_{ab^{-1}}$ move $bV$ to $aV$").

Setting: `X = S.carrier` an infinite minimal subshift over a finite discrete alphabet, `T` the shift,
`R = LC(X, F₂) ⋊_T ℤ`, `G_X = EL_3(R)`.

* A **clopen tower of height `2w+1`** is a nonempty clopen `V` whose translates `T^{a-w} V`,
  `a < 2w+1`, are pairwise disjoint (`LevelsDisjoint`); `exists_clopen_tower` produces one for
  every `w` (no periodic points, total separatedness).
* The **copy of `GL_d(F₂)`**, `d = 3(2w+1)`, is `towerCopyG`: the monoid hom
  `GL_{Fin 3 × Fin (2w+1)}(F₂) → G_X` obtained from the tower matrix units
  `ε_{ab} = e_{T^{a-w}V} u^{a-b}` (`towerE`), which is injective (`towerCopyG_injective`) and sends
  the transvection `I + E_{(p,a),(q,b)}` to the elementary matrix `e_{pq}(ε_{ab})`
  (`towerCopyG_transvection`).  `GL_d(F₂)` is simple for `d ≥ 3` (in-repo proof).
* `manuscriptSentence_normalSubgroupContainsTowerCommutator` (l.120–123): every nontrivial normal
  `K ≤ G_X` contains `[c x, c y] ≠ 1` for the copy `c` over a clopen tower.  Route: `G_X` is simple
  (closed, unconditional `isSimpleGroup_elementaryGroup_stepanov`), so `K = G_X`; the commutator is
  the image of a noncommuting pair in `GL_d(F₂)` (trivial centre), nontrivial by injectivity.
* `manuscriptSentence_containsCopyElementaryMatrixEveryElementary` (l.123–124): if `K` is normal
  and contains a nontrivial element of the copy `c`, then `K` contains the whole copy (simplicity of
  `GL_d(F₂)`), hence the elementary matrices `e_{pq}(e_V) = c(I + E_{(p,w),(q,w)})`, and then every
  elementary matrix `e_{pq}(r)`: the level ideal `J = {r | e_{pq}(r) ∈ K ∀ p ≠ q}` contains `e_V`,
  and minimality plus compactness give `1 ∈ J`.  This is the printed route.
* `manuscriptSentence_figureTowerMatrixUnits` (l.150–156): the picture — disjoint translates of a
  small clopen set, and the matrix units `ε_{ab}` carrying `e_{bV}` to `e_{aV}`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ThmMainB

open SymbolicDynamics.FullShift ClopenCrossedProduct Pestov91.SimpleModCentre
open scoped commutatorElement

/-- **A clopen tower of any height**: a nonempty clopen set with pairwise disjoint translates
`T^{a-w} V`, `a < 2w + 1`. -/
theorem exists_clopen_tower {A : Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (S : Subshift A ℤ) (hinf : Infinite S.carrier) (hmin : IsMinimal S) (w : ℕ) :
    ∃ V : Set S.carrier, IsClopen V ∧ V.Nonempty ∧ LevelsDisjoint (subshiftHomeo S) w V := by
  haveI := compactSpace_carrier S
  obtain ⟨y⟩ := hinf.nonempty
  obtain ⟨V, hV, hyV, hdisj⟩ := exists_clopen_nbhd_disjoint_translates (subshiftHomeo S)
    (subshiftHomeo_zpow_ne_self S hinf hmin) (2 * w) y
  refine ⟨V, hV, ⟨y, hyV⟩, ?_⟩
  intro a b hab
  rw [Set.disjoint_left]
  rintro _ ⟨v, hv, rfl⟩ ⟨v', hv', hvv'⟩
  have hj0 : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ≠ 0 := fun h => hab (Fin.ext (by omega))
  have ha := a.isLt
  have hb := b.isLt
  have hjL : |((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)| ≤ ((2 * w : ℕ) : ℤ) :=
    abs_le.2 ⟨by omega, by omega⟩
  refine Set.disjoint_left.1 (hdisj _ hj0 hjL) hv ⟨v', hv', ?_⟩
  calc (subshiftHomeo S ^ (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) v'
      = (subshiftHomeo S ^ (-(((a : ℕ) : ℤ) - (w : ℤ))))
          ((subshiftHomeo S ^ (((b : ℕ) : ℤ) - (w : ℤ))) v') := by
        rw [← Homeomorph.mul_apply, ← zpow_add,
          show -(((a : ℕ) : ℤ) - (w : ℤ)) + (((b : ℕ) : ℤ) - (w : ℤ)) =
            ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) by ring]
    _ = (subshiftHomeo S ^ (-(((a : ℕ) : ℤ) - (w : ℤ))))
          ((subshiftHomeo S ^ (((a : ℕ) : ℤ) - (w : ℤ))) v) := by rw [hvv']
    _ = v := by
        rw [← Homeomorph.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Homeomorph.one_apply]

/-- `d = |Fin 3 × Fin (2w+1)| ≥ 3`. -/
theorem card_tower_ge_three (w : ℕ) : 3 ≤ Fintype.card (Fin 3 × Fin (2 * w + 1)) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  omega

/-- **The copy of `GL_d(F₂)` over a clopen tower**, `d = 3(2w+1)`, as a monoid hom into `G_X`. -/
noncomputable def towerCopyG {A : Type} [TopologicalSpace A] (S : Subshift A ℤ) {w : ℕ}
    {V : Set S.carrier} (hlev : LevelsDisjoint (subshiftHomeo S) w V) (hV : IsClopen V) :
    (Matrix (Fin 3 × Fin (2 * w + 1)) (Fin 3 × Fin (2 * w + 1)) (ZMod 2))ˣ →* G S :=
  (towerCopy (Fin 3) hlev subset_rfl hV).codRestrict _
    (towerCopy_mem_elementaryGroup hlev subset_rfl hV)

/-- The copy is injective over a nonempty tower base. -/
theorem towerCopyG_injective {A : Type} [TopologicalSpace A] (S : Subshift A ℤ) {w : ℕ}
    {V : Set S.carrier} (hlev : LevelsDisjoint (subshiftHomeo S) w V) (hV : IsClopen V)
    (hne : V.Nonempty) : Function.Injective (towerCopyG S hlev hV) := by
  intro x y hxy
  exact towerCopy_injective (ι := Fin 3) hlev subset_rfl hV hne (congrArg Subtype.val hxy)

/-- The copy sends the transvection `I + E_{(p,a),(q,b)}` to the elementary matrix `e_{pq}(ε_{ab})`. -/
theorem towerCopyG_transvection {A : Type} [TopologicalSpace A] (S : Subshift A ℤ) {w : ℕ}
    {V : Set S.carrier} (hlev : LevelsDisjoint (subshiftHomeo S) w V) (hV : IsClopen V)
    {p q : Fin 3} (hpq : p ≠ q) (a b : Fin (2 * w + 1)) (h : (p, a) ≠ (q, b)) :
    towerCopyG S hlev hV (elementaryUnit (p, a) (q, b) h (1 : ZMod 2)) =
      elGen p q hpq (towerE (subshiftHomeo S) (ZMod 2) w hV a b) :=
  Subtype.ext (towerCopy_transvection hlev subset_rfl hV hpq a b h)

/-- **tex l.120–123.** A nontrivial normal subgroup `K` of `G_X` contains a nontrivial commutator
lying in a copy of the finite simple group `GL_d(F₂)`, `d = 3(2w+1)`, over a clopen tower: a nonempty
clopen set `V` with pairwise disjoint translates `T^{a-w} V`.  The copy is injective and built from
the tower matrix units `ε_{ab}`. -/
theorem manuscriptSentence_normalSubgroupContainsTowerCommutator (A : Type) [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) (K : Subgroup (G S)) (hK : K.Normal) (hne : K ≠ ⊥) (w : ℕ) :
    ∃ (V : Set S.carrier) (hV : IsClopen V) (hlev : LevelsDisjoint (subshiftHomeo S) w V),
      V.Nonempty ∧
      IsSimpleGroup (Matrix (Fin 3 × Fin (2 * w + 1)) (Fin 3 × Fin (2 * w + 1)) (ZMod 2))ˣ ∧
      Function.Injective (towerCopyG S hlev hV) ∧
      (∀ (p q : Fin 3) (hpq : p ≠ q) (a b : Fin (2 * w + 1)) (h : (p, a) ≠ (q, b)),
        towerCopyG S hlev hV (elementaryUnit (p, a) (q, b) h (1 : ZMod 2)) =
          elGen p q hpq (towerE (subshiftHomeo S) (ZMod 2) w hV a b)) ∧
      ∃ x y : (Matrix (Fin 3 × Fin (2 * w + 1)) (Fin 3 × Fin (2 * w + 1)) (ZMod 2))ˣ,
        ⁅towerCopyG S hlev hV x, towerCopyG S hlev hV y⁆ ∈ K ∧
          ⁅towerCopyG S hlev hV x, towerCopyG S hlev hV y⁆ ≠ 1 := by
  obtain ⟨V, hV, hVne, hlev⟩ := exists_clopen_tower S hinf hmin w
  haveI := isSimpleGroup_elementaryGroup_stepanov S hinf hmin (le_refl 3)
  have htop : K = ⊤ := hK.eq_bot_or_eq_top.resolve_left hne
  have hcardd := card_tower_ge_three w
  haveI := FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo (Fin 3 × Fin (2 * w + 1)) hcardd
  have hinj : Function.Injective (towerCopyG S hlev hV) := towerCopyG_injective S hlev hV hVne
  obtain ⟨x, hx⟩ :=
    exists_ne (1 : (Matrix (Fin 3 × Fin (2 * w + 1)) (Fin 3 × Fin (2 * w + 1)) (ZMod 2))ˣ)
  have hxc : x ∉
      Subgroup.center (Matrix (Fin 3 × Fin (2 * w + 1)) (Fin 3 × Fin (2 * w + 1)) (ZMod 2))ˣ := by
    rw [center_units_matrix_zmodTwo_eq_bot _ hcardd, Subgroup.mem_bot]
    exact hx
  have hnc : ¬∀ g, g * x = x * g := fun h => hxc (Subgroup.mem_center_iff.2 h)
  obtain ⟨y, hy⟩ := not_forall.1 hnc
  have hxy : ⁅x, y⁆ ≠ 1 := fun h => hy (commutatorElement_eq_one_iff_mul_comm.1 h).symm
  refine ⟨V, hV, hlev, hVne, inferInstance, hinj,
    fun p q hpq a b h => towerCopyG_transvection S hlev hV hpq a b h, x, y, ?_, ?_⟩
  · rw [htop]
    exact Subgroup.mem_top _
  · rw [← map_commutatorElement (towerCopyG S hlev hV)]
    exact fun h => hxy (hinj (h.trans (map_one _).symm))

/-- **tex l.123–124.** If a normal subgroup `K` of `G_X` contains a nontrivial element of the copy of
`GL_d(F₂)` over a clopen tower `V`, then it contains this group, with it the elementary matrices
`e_{pq}(e_V)` (images of transvections), and, by minimality, every elementary matrix `e_{pq}(r)`,
`r ∈ R`. -/
theorem manuscriptSentence_containsCopyElementaryMatrixEveryElementary (A : Type)
    [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ) (hmin : IsMinimal S)
    (K : Subgroup (G S)) (hK : K.Normal) {w : ℕ} {V : Set S.carrier} (hV : IsClopen V)
    (hlev : LevelsDisjoint (subshiftHomeo S) w V) (hVne : V.Nonempty) (g : G S) (hgK : g ∈ K)
    (hg1 : g ≠ 1) (hgc : g ∈ (towerCopyG S hlev hV).range) :
    (∀ x, towerCopyG S hlev hV x ∈ K) ∧
    (∀ (p q : Fin 3) (hpq : p ≠ q),
      elGen p q hpq
        (ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV))
        ∈ K) ∧
    ∀ (p q : Fin 3) (hpq : p ≠ q) (r : R S), elGen p q hpq r ∈ K := by
  haveI := hK
  haveI := compactSpace_carrier S
  haveI := FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo (Fin 3 × Fin (2 * w + 1))
    (card_tower_ge_three w)
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hgc
  have hx1 : x ≠ 1 := fun h => hg1 (by rw [h, map_one])
  have hxK : x ∈ K.comap (towerCopyG S hlev hV) := hgK
  have htop : K.comap (towerCopyG S hlev hV) = ⊤ :=
    (hK.comap _).eq_bot_or_eq_top.resolve_left fun hb => hx1 (Subgroup.mem_bot.1 (hb ▸ hxK))
  have hall : ∀ y, towerCopyG S hlev hV y ∈ K := fun y => by
    have hy : y ∈ K.comap (towerCopyG S hlev hV) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hy
  have hroot : ∀ (p q : Fin 3) (hpq : p ≠ q),
      elGen p q hpq
        (ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) (LocallyConstant.charFn (ZMod 2) hV))
        ∈ K := by
    intro p q hpq
    have hne' : ((p, ⟨w, by omega⟩) : Fin 3 × Fin (2 * w + 1)) ≠ (q, ⟨w, by omega⟩) := by
      simp [hpq]
    rw [← towerE_centre (T := subshiftHomeo S) w hV,
      ← towerCopyG_transvection S hlev hV hpq _ _ hne']
    exact hall _
  have hcard : 3 ≤ Fintype.card (Fin 3) := (Fintype.card_fin 3).ge
  have hmemJ : ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2)
      (LocallyConstant.charFn (ZMod 2) hV) ∈ levelIdeal hcard K :=
    (mem_levelIdeal hcard K _).2 hroot
  obtain ⟨s, hs⟩ :=
    exists_finset_cover_zpow_image (isMinimalSystem_subshiftHomeo S hmin) hV.isOpen hVne
  have h1 := one_mem_levelIdeal_of_cover hcard hV s hs K hmemJ
  refine ⟨hall, hroot, fun p q hpq r => ?_⟩
  have hd := TwoSidedIdeal.mul_mem_left _ r 1 h1
  rw [mul_one] at hd
  exact (mem_levelIdeal hcard K r).1 hd p q hpq

/-- **Figure (b), tex l.150–156** (caption l.163–165).  A small clopen set `V` with pairwise
disjoint translates `T^{a-w} V`, and the matrix units `ε_{ab} = e_{T^{a-w}V} u^{a-b}`, which move
`T^{b-w}V` to `T^{a-w}V`: `e_{aV} ε_{ab} = ε_{ab} = ε_{ab} e_{bV}`, `ε_{ab} ε_{ba} = e_{aV}`, where
`ε_{aa} = e_{aV}` is the indicator of the level `T^{a-w}V`. -/
theorem manuscriptSentence_figureTowerMatrixUnits {A : Type} [TopologicalSpace A]
    (S : Subshift A ℤ) {w : ℕ} {V : Set S.carrier} (hV : IsClopen V)
    (hlev : LevelsDisjoint (subshiftHomeo S) w V) :
    (∀ a b : Fin (2 * w + 1), a ≠ b →
      Disjoint (⇑(subshiftHomeo S ^ (((a : ℕ) : ℤ) - (w : ℤ))) '' V)
        (⇑(subshiftHomeo S ^ (((b : ℕ) : ℤ) - (w : ℤ))) '' V)) ∧
    (∀ a b : Fin (2 * w + 1),
      towerE (subshiftHomeo S) (ZMod 2) w hV a a * towerE (subshiftHomeo S) (ZMod 2) w hV a b =
          towerE (subshiftHomeo S) (ZMod 2) w hV a b ∧
        towerE (subshiftHomeo S) (ZMod 2) w hV a b * towerE (subshiftHomeo S) (ZMod 2) w hV b b =
          towerE (subshiftHomeo S) (ZMod 2) w hV a b ∧
        towerE (subshiftHomeo S) (ZMod 2) w hV a b * towerE (subshiftHomeo S) (ZMod 2) w hV b a =
          towerE (subshiftHomeo S) (ZMod 2) w hV a a) ∧
    ∀ a : Fin (2 * w + 1),
      towerE (subshiftHomeo S) (ZMod 2) w hV a a =
        ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2)
          (LocallyConstant.charFn (ZMod 2)
            (isClopen_image (subshiftHomeo S ^ (((a : ℕ) : ℤ) - (w : ℤ))) hV)) := by
  refine ⟨hlev, fun a b => ⟨?_, ?_, ?_⟩, fun a => towerE_self w hV a⟩
  · rw [towerE_mul_towerE hlev subset_rfl subset_rfl hV hV, if_pos rfl, towerE_inter_self]
  · rw [towerE_mul_towerE hlev subset_rfl subset_rfl hV hV, if_pos rfl, towerE_inter_self]
  · rw [towerE_mul_towerE hlev subset_rfl subset_rfl hV hV, if_pos rfl, towerE_inter_self]

end ThmMainB
end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainB.manuscriptSentence_normalSubgroupContainsTowerCommutator
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainB.manuscriptSentence_containsCopyElementaryMatrixEveryElementary
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainB.manuscriptSentence_figureTowerMatrixUnits
