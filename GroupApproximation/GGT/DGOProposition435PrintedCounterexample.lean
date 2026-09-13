import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import GroupApproximation.GGT.DGOProposition435Printed
import GroupApproximation.Meta.AxiomGuard

/-!
# The Lean spelling of DGO Proposition 4.35, printed direction, is false

`RelHyp.DGOProposition435PrintedStatement` in `GGT/DGOProposition435Printed.lean`
transcribes Dahmani--Guirardel--Osin, Proposition 4.35 (`\label{transitive}` at
`HE.tex:976` of arXiv `1111.7048`). `non_mf_groups_exist.tex` does not cite that
proposition by number. The conclusion of the Lean statement asks for a `RelGenSet`
whose base is exactly `X ∪ ⋃_λ Y_λ`.

This file refutes that Lean spelling. It does not refute DGO's printed
Proposition 4.35. A `RelGenSet` needs its base together with its members to be
closed under inversion. When every `M_λ` is empty, the conclusion has no members, so
the forced base `X ∪ ⋃_λ Y_λ` would have to be closed under inversion on its own. `X`
need not be, since the hypothesis only asks `X ∪ ⋃_λ H_λ` to be. So the forced base
is not inversion-closed, and no `RelGenSet` has it.

The counterexample is `G = ZMod 5` written multiplicatively and lifted to `Type u`,
with `t` the image of `1`:

* the one member `H = G` over `X = {t²}`, hyperbolically embedded because its
  Cayley graph has diameter at most one and `G` is finite;
* the empty subfamily of `H` over `Y = {t, t⁻¹}`, hyperbolically embedded because
  the Cayley graph of a cyclic group over a generator is hyperbolic
  (`CyclicCayley.exists_isHyperbolicSpace_cayley_of_zpowers`).

The forced base is `{t², t, t⁻¹}`, and it does not contain `t⁻²`.

Three theorems of `GGT/DGOProposition435Printed.lean` take this statement as a
hypothesis `h435` at universes `.{u, 0, w}`, so they are vacuous and carry nothing:
`isRelativelyHyperbolic_original_of_jointPreservation` (line 315),
`isRelativelyHyperbolic_original_of_jointPreservation_of_cyclic` (line 404) and
`canonicalQuotientFamilyPreservation_of_jointPreservation` (line 561).
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

namespace DGOProposition435PrintedCounterexample

/-- `ZMod 5`, written multiplicatively and lifted to `Type u`. -/
abbrev G5 : Type u := ULift.{u} (Multiplicative (ZMod 5))

/-- The generator `t`, the image of `1 : ZMod 5`. -/
def t5 : G5.{u} := ULift.up (Multiplicative.ofAdd 1)

/-- Every element of `G5` is a power of `t`. -/
theorem exists_zpow_eq (g : G5.{u}) : ∃ k : ℤ, t5 ^ k = g := by
  have key : ∀ x : Multiplicative (ZMod 5), ∃ n : ℕ,
      Multiplicative.ofAdd (1 : ZMod 5) ^ n = x := by
    intro x
    refine ⟨(Multiplicative.toAdd x).val, ?_⟩
    apply Multiplicative.toAdd.injective
    simp
  obtain ⟨n, hn⟩ := key g.down
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  exact ULift.ext _ _ hn

/-- The forced base `{t², t, t⁻¹}` does not contain `t⁻²`. -/
theorem t5_inv_ne :
    (t5.{u} * t5)⁻¹ ≠ t5 * t5 ∧ t5.{u} ≠ (t5 * t5)⁻¹ ∧ t5.{u}⁻¹ ≠ (t5 * t5)⁻¹ := by
  decide

/-- The one-member family `H = G` over the base `X = {t²}`. -/
def fiveRelGenSet : RelGenSet G5.{u} PUnit.{w+1} where
  base := {t5 * t5}
  fam := fun _ => ⊤
  symmetricGenerating := by
    constructor
    · intro x _
      exact Or.inr (Set.mem_iUnion.mpr ⟨PUnit.unit, Subgroup.mem_top x⁻¹⟩)
    · rw [eq_top_iff]
      intro x _
      exact Subgroup.subset_closure
        (Or.inr (Set.mem_iUnion.mpr ⟨PUnit.unit, Subgroup.mem_top x⟩))

/-- `H = G` is hyperbolically embedded in `G` over `X = {t²}`: every vertex of the
Cayley graph is within one letter of every other, and `G` is finite. -/
theorem fiveRelGenSet_isHyperbolicallyEmbedded :
    (fiveRelGenSet : RelGenSet G5.{u} PUnit.{w+1}).IsHyperbolicallyEmbedded := by
  refine ⟨⟨1, ?_⟩, fun _ _ => ?_⟩
  · refine isHyperbolicSpace_of_bounded ?_
    intro x y
    have hmem : ((Cayley.val x)⁻¹ * Cayley.val y : G5.{u}) ∈
        (fiveRelGenSet : RelGenSet G5.{u} PUnit.{w+1}).alphabet.carrier :=
      Or.inr (Set.mem_iUnion.mpr ⟨PUnit.unit, Subgroup.mem_top _⟩)
    have hnorm : WordMetric.wordNorm
        (fiveRelGenSet : RelGenSet G5.{u} PUnit.{w+1}).alphabet.carrier
        ((Cayley.val x)⁻¹ * Cayley.val y) ≤ 1 :=
      WordMetric.wordNorm_le_one_of_mem hmem
    rw [Cayley.dist_eq]
    exact_mod_cast hnorm
  · exact Set.toFinite _

/-- The generator `t` as an element of the member `H = ⊤`. -/
def tTop : ↥(⊤ : Subgroup G5.{u}) := ⟨t5, Subgroup.mem_top _⟩

theorem tTop_zpowers (x : ↥(⊤ : Subgroup G5.{u})) :
    x ∈ Subgroup.zpowers tTop := by
  obtain ⟨k, hk⟩ := exists_zpow_eq x.val
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_zpow]
  exact hk

/-- The empty subfamily of `H = ⊤` over `Y = {t, t⁻¹}`. -/
def pairRelGenSet : RelGenSet ↥(⊤ : Subgroup G5.{u}) PEmpty.{v+1} where
  base := CyclicCayley.pairSet tTop
  fam := PEmpty.elim
  symmetricGenerating := by
    have hunion : CyclicCayley.pairSet tTop ∪
        (⋃ e : PEmpty.{v+1}, ((PEmpty.elim e : Subgroup ↥(⊤ : Subgroup G5.{u})) :
          Set ↥(⊤ : Subgroup G5.{u}))) = CyclicCayley.pairSet tTop := by
      rw [Set.iUnion_of_empty, Set.union_empty]
    rw [hunion]
    exact CyclicCayley.isSymmetricGeneratingSet_pairSet tTop tTop_zpowers

theorem pairRelGenSet_alphabet_carrier :
    (pairRelGenSet : RelGenSet ↥(⊤ : Subgroup G5.{u}) PEmpty.{v+1}).alphabet.carrier =
      CyclicCayley.pairSet tTop := by
  show CyclicCayley.pairSet tTop ∪
      (⋃ e : PEmpty.{v+1}, ((PEmpty.elim e : Subgroup ↥(⊤ : Subgroup G5.{u})) :
        Set ↥(⊤ : Subgroup G5.{u}))) = CyclicCayley.pairSet tTop
  rw [Set.iUnion_of_empty, Set.union_empty]

/-- The empty subfamily of `H` over `{t, t⁻¹}` is hyperbolically embedded in `H`:
the Cayley graph of a cyclic group over a generator is hyperbolic, and local
finiteness is vacuous. -/
theorem pairRelGenSet_isHyperbolicallyEmbedded :
    (pairRelGenSet : RelGenSet ↥(⊤ : Subgroup G5.{u}) PEmpty.{v+1}).IsHyperbolicallyEmbedded :=
  ⟨CyclicCayley.exists_isHyperbolicSpace_cayley_of_zpowers tTop_zpowers _
    pairRelGenSet_alphabet_carrier, fun e => PEmpty.elim e⟩

end DGOProposition435PrintedCounterexample

open DGOProposition435PrintedCounterexample in
/-- **The Lean spelling of DGO Proposition 4.35, printed direction, is false** at
every universe. The forced base `{t², t, t⁻¹}` of the counterexample in `ZMod 5`
is not closed under inversion, and the conclusion has no members to absorb `t⁻²`.
This refutes `DGOProposition435PrintedStatement`, not DGO's printed
Proposition 4.35. -/
theorem not_dgoProposition435PrintedStatement :
    ¬ DGOProposition435PrintedStatement.{u, v, w} := by
  intro h
  unfold DGOProposition435PrintedStatement at h
  obtain ⟨Z, hZbase, -, -⟩ :=
    h (fiveRelGenSet : RelGenSet G5.{u} PUnit.{w+1}) (M := fun _ => PEmpty.{v+1})
      (fun _ => pairRelGenSet) fiveRelGenSet_isHyperbolicallyEmbedded
      (fun _ => pairRelGenSet_isHyperbolicallyEmbedded)
  have hs : (t5.{u} * t5) ∈ Z.base := by
    rw [hZbase]
    exact Or.inl (Set.mem_singleton _)
  have hinv := Z.symmetricGenerating.inv_mem _ (Or.inl hs)
  rcases hinv with hbase | hfam
  · rw [hZbase] at hbase
    rcases hbase with hX | hY
    · exact t5_inv_ne.1 hX
    · obtain ⟨_, x, hx, hxs⟩ := Set.mem_iUnion.mp hY
      rcases CyclicCayley.mem_pairSet_iff.mp hx with rfl | rfl
      · exact t5_inv_ne.2.1 hxs
      · exact t5_inv_ne.2.2 hxs
  · obtain ⟨p, -⟩ := Set.mem_iUnion.mp hfam
    exact PEmpty.elim p.2

end RelHyp
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.RelHyp.DGOProposition435PrintedCounterexample.fiveRelGenSet_isHyperbolicallyEmbedded
#audit_axioms GroupApproximation.GGT.RelHyp.DGOProposition435PrintedCounterexample.pairRelGenSet_isHyperbolicallyEmbedded
#audit_axioms GroupApproximation.GGT.RelHyp.not_dgoProposition435PrintedStatement
