import Mathlib.Algebra.Colimit.DirectLimit
import GroupApproximation.Meta.AxiomGuard

/-!
# Canonical stage maps into Mathlib's group `DirectLimit`

`non_mf_groups_exist.tex`, Theorem `thm:amenable-trace`, tex 284–286:

> Since $W_0$ is a direct limit of residually finite groups, it is MF~\cite[Corollary~10 and
> Proposition~13]{Korchagin}.

Korchagin's Proposition 13 is proved in subgroup-range form in
`Manuscript/NonMF/IntroAmenable/KorchaginDirectLimit.lean`
(`IntroAmenable.isOperatorMF_of_injective_directLimit`).  This module supplies the interface
needed to apply it to Mathlib's generic `DirectLimit G f` (`Mathlib/Order/DirectedInverseSystem.lean`,
group instance in `Mathlib/Algebra/Colimit/DirectLimit.lean`), for a directed system of groups
`f i j h : G i →* G j`:

* `of G f i : G i →* DirectLimit G f`, `x ↦ ⟦⟨i, x⟩⟧` (Mathlib has no group-level `of`);
* `of_f`: compatibility with the connecting maps (`DirectLimit.mk_apply`);
* `of_injective`: injective connecting maps give injective stage maps (`DirectLimit.mk_injective`);
* `range_of_directed`: the stage ranges form a directed family (`exists_ge_ge`);
* `exists_mem_range_of`: the stage ranges cover the limit (`DirectLimit.exists_eq_mk`);
* `countable_directLimit`: a countably indexed limit of countable groups is countable, as a
  quotient of the countable sigma type.

All statements carry explicit binders (no section variables).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto01

/-- The canonical homomorphism from the stage `G i` into the group direct limit,
`x ↦ ⟦⟨i, x⟩⟧`. -/
noncomputable def of {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type) [∀ i, Group (G i)] (f : ∀ i j, i ≤ j → G i →* G j)
    [DirectedSystem G fun i j h ↦ f i j h] (i : ι) : G i →* DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (DirectLimit.one_def i).symm
  map_mul' x y := (DirectLimit.mul_def i x y).symm

/-- `of` evaluates to the class of the pair `⟨i, x⟩`. -/
theorem of_apply {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type) [∀ i, Group (G i)] (f : ∀ i j, i ≤ j → G i →* G j)
    [DirectedSystem G fun i j h ↦ f i j h] (i : ι) (x : G i) :
    of G f i x = (⟦⟨i, x⟩⟧ : DirectLimit G f) :=
  rfl

/-- The stage maps are compatible with the connecting maps. -/
theorem of_f {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type) [∀ i, Group (G i)] (f : ∀ i j, i ≤ j → G i →* G j)
    [DirectedSystem G fun i j h ↦ f i j h] {i j : ι} (h : i ≤ j) (x : G i) :
    of G f j (f i j h x) = of G f i x := by
  rw [of_apply, of_apply]
  exact DirectLimit.mk_apply i j x h

/-- If every connecting map is injective, every stage map into the direct limit is injective. -/
theorem of_injective {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type) [∀ i, Group (G i)] (f : ∀ i j, i ≤ j → G i →* G j)
    [DirectedSystem G fun i j h ↦ f i j h]
    (hinj : ∀ i j h, Function.Injective (f i j h)) (i : ι) :
    Function.Injective (of G f i) :=
  DirectLimit.mk_injective f hinj i

/-- The stage ranges increase along the order. -/
theorem range_of_le_range_of {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type) [∀ i, Group (G i)] (f : ∀ i j, i ≤ j → G i →* G j)
    [DirectedSystem G fun i j h ↦ f i j h] {i j : ι} (h : i ≤ j) :
    (of G f i).range ≤ (of G f j).range := by
  intro y hy
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
  exact MonoidHom.mem_range.mpr ⟨f i j h x, of_f G f h x⟩

/-- The stage ranges form a directed family of subgroups. -/
theorem range_of_directed {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type) [∀ i, Group (G i)] (f : ∀ i j, i ≤ j → G i →* G j)
    [DirectedSystem G fun i j h ↦ f i j h] (i j : ι) :
    ∃ k, (of G f i).range ≤ (of G f k).range ∧ (of G f j).range ≤ (of G f k).range := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  exact ⟨k, range_of_le_range_of G f hik, range_of_le_range_of G f hjk⟩

/-- Every element of the direct limit lies in some stage range. -/
theorem exists_mem_range_of {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type) [∀ i, Group (G i)] (f : ∀ i j, i ≤ j → G i →* G j)
    [DirectedSystem G fun i j h ↦ f i j h] (z : DirectLimit G f) :
    ∃ i, z ∈ (of G f i).range := by
  obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk (f := f) z
  exact ⟨i, MonoidHom.mem_range.mpr ⟨x, of_apply G f i x⟩⟩

/-- A countably indexed direct limit of countable groups is countable: it is a quotient of the
countable sigma type `Σ i, G i`. -/
theorem countable_directLimit {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Countable ι]
    (G : ι → Type) [∀ i, Group (G i)] [∀ i, Countable (G i)]
    (f : ∀ i j, i ≤ j → G i →* G j) [DirectedSystem G fun i j h ↦ f i j h] :
    Countable (DirectLimit G f) :=
  Quotient.mk''_surjective.countable

end IntroCarto01
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto01.of_apply
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto01.of_f
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto01.of_injective
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto01.range_of_le_range_of
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto01.range_of_directed
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto01.exists_mem_range_of
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto01.countable_directLimit
