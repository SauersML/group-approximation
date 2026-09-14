import GroupApproximation.Meta.AxiomGuard
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Connected.Separation
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Data.ZMod.Defs

/-!
# Small clopen sets for a topologically free action

`simple_kazhdan_sofic_group.tex` at 37551fd93, `\label{sec:proof}`, subsection "Simplicity", tex
l.152–159 (the proof of the simplicity clause of `thm:general`):

> Let $1\ne K\trianglelefteq G$ and $1\ne g\in K$, and let $w\ge0$ bound the word lengths of the
> $\xi$ with $u_\xi$ occurring in the entries of $g$ and $g^{-1}$. Call a clopen set $V$ small if
> $V\cap\xi V=\varnothing$ for $\xi\in B_{2w}\setminus\{e\}$ and every $f\circ\xi$, with
> $\xi\in B_w$ and $f$ a coefficient of an entry of $g$ or $g^{-1}$, is constant on $V$. Each
> $\xi\ne e$ fixes a closed set with empty interior, so the points moved by every
> $\xi\in B_{2w}\setminus\{e\}$ are dense, and every nonempty clopen set contains a nonempty small
> one.

The group `Λ` acts on `Z` by homeomorphisms.  `thm:general` defines topological freeness (tex
l.106–107) as: no nontrivial element fixes a nonempty open set, i.e. `interior {z | ξ • z = z} = ∅`
for `ξ ≠ e`.  The balls are finite sets: `D` for `B_{2w}` and `B` for `B_w`, which covers the
printed word-length balls.

* `IsSmall D B F V`: the printed "small", for a finite set `F` of coefficient functions;
* `IsSmall.mono`: subsets of small sets are small;
* `isClosed_fixed`: each `ξ` fixes a closed set;
* `dense_moved`: the points moved by every `ξ ∈ D ∖ {e}` are dense;
* `exists_isSmall_subset`: every nonempty clopen set contains a nonempty small one;
* the closed endpoint `printedGeneralSmallSets`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace General

open scoped Pointwise

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z]

/-- **Small** (tex l.154–156): `V ∩ ξV = ∅` for `ξ ∈ D ∖ {e}`, and every `f ∘ ξ`, `ξ ∈ B`, `f ∈ F`,
is constant on `V`. -/
def IsSmall (D B : Finset Λ) (F : Finset (LocallyConstant Z (ZMod 2))) (V : Set Z) : Prop :=
  (∀ ξ ∈ D, ξ ≠ 1 → Disjoint V (ξ • V)) ∧
    ∀ f ∈ F, ∀ ξ ∈ B, ∀ x ∈ V, ∀ y ∈ V, f (ξ • x) = f (ξ • y)

/-- Subsets of small sets are small. -/
theorem IsSmall.mono {D B : Finset Λ} {F : Finset (LocallyConstant Z (ZMod 2))} {U V : Set Z}
    (hVU : V ⊆ U) (hU : IsSmall D B F U) : IsSmall D B F V :=
  ⟨fun ξ hξ h1 => (hU.1 ξ hξ h1).mono hVU (Set.image_mono hVU),
    fun f hf ξ hξ x hx y hy => hU.2 f hf ξ hξ x (hVU hx) y (hVU hy)⟩

variable [ContinuousConstSMul Λ Z]

/-- **tex l.157**: each `ξ` fixes a closed set. -/
theorem isClosed_fixed [T2Space Z] (ξ : Λ) : IsClosed {z : Z | ξ • z = z} :=
  isClosed_eq (continuous_const_smul ξ) continuous_id

/-- **tex l.157–158**: if every `ξ ≠ e` fixes a set with empty interior, the points moved by every
`ξ ∈ D ∖ {e}` are dense. -/
theorem dense_moved [T2Space Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D : Finset Λ) :
    Dense {z : Z | ∀ ξ ∈ D, ξ ≠ 1 → ξ • z ≠ z} := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    have h : {z : Z | ∀ ξ ∈ (∅ : Finset Λ), ξ ≠ 1 → ξ • z ≠ z} = Set.univ := by
      ext z
      simp
    rw [h]
    exact dense_univ
  | insert ξ D hξ ih =>
    have hset : {z : Z | ξ ≠ 1 → ξ • z ≠ z} =
        if ξ = 1 then Set.univ else {z : Z | ξ • z = z}ᶜ := by
      split_ifs with h1
      · ext z
        simp [h1]
      · ext z
        simp [h1]
    have hopen : IsOpen {z : Z | ξ ≠ 1 → ξ • z ≠ z} := by
      rw [hset]
      split_ifs
      · exact isOpen_univ
      · exact (isClosed_fixed ξ).isOpen_compl
    have hdense : Dense {z : Z | ξ ≠ 1 → ξ • z ≠ z} := by
      rw [hset]
      split_ifs with h1
      · exact dense_univ
      · exact interior_eq_empty_iff_dense_compl.mp (hfree ξ h1)
    have heq : {z : Z | ∀ η ∈ insert ξ D, η ≠ 1 → η • z ≠ z} =
        {z : Z | ξ ≠ 1 → ξ • z ≠ z} ∩ {z : Z | ∀ η ∈ D, η ≠ 1 → η • z ≠ z} := by
      ext z
      simp only [Finset.mem_insert, forall_eq_or_imp, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [heq]
    exact hdense.inter_of_isOpen_left ih hopen

/-- **tex l.157–159**: for a topologically free action on a totally separated space, every nonempty
clopen set contains a nonempty small one. -/
theorem exists_isSmall_subset [TotallySeparatedSpace Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {A : Set Z} (hA : IsClopen A) (hne : A.Nonempty) :
    ∃ V : Set Z, IsClopen V ∧ V.Nonempty ∧ V ⊆ A ∧ IsSmall D B F V := by
  classical
  obtain ⟨x, hxm, hxA⟩ := (dense_moved hfree D).exists_mem_open hA.isOpen hne
  have hsep : ∀ ξ ∈ D, ∃ C : Set Z, ξ ≠ 1 → IsClopen C ∧ x ∈ C ∧ ξ • x ∈ Cᶜ := by
    intro ξ hξ
    by_cases h1 : ξ = 1
    · exact ⟨Set.univ, fun h => absurd h1 h⟩
    · obtain ⟨C, hC, hxC, hyC⟩ := exists_isClopen_of_totally_separated (hxm ξ hξ h1).symm
      exact ⟨C, fun _ => ⟨hC, hxC, hyC⟩⟩
  choose! C hC using hsep
  refine ⟨A ∩ (⋂ ξ ∈ D.filter (fun ξ => ξ ≠ 1), (C ξ ∩ (fun z => ξ • z) ⁻¹' (C ξ)ᶜ)) ∩
      ⋂ p ∈ F ×ˢ B, (fun z => p.2 • z) ⁻¹' {y | p.1 y = p.1 (p.2 • x)}, ?_, ⟨x, ?_⟩,
    fun z hz => hz.1.1, ?_⟩
  · refine (hA.inter (isClopen_biInter_finset fun ξ hξ => ?_)).inter
      (isClopen_biInter_finset fun p _ => ?_)
    · have h1 := Finset.mem_filter.mp hξ
      obtain ⟨hCc, -, -⟩ := hC ξ h1.1 h1.2
      exact hCc.inter (hCc.compl.preimage (continuous_const_smul ξ))
    · exact (p.1.isLocallyConstant.isClopen_fiber _).preimage (continuous_const_smul p.2)
  · refine ⟨⟨hxA, Set.mem_iInter₂.mpr fun ξ hξ => ?_⟩, Set.mem_iInter₂.mpr fun p _ => rfl⟩
    have h1 := Finset.mem_filter.mp hξ
    obtain ⟨-, hxC, hyC⟩ := hC ξ h1.1 h1.2
    exact ⟨hxC, hyC⟩
  · refine ⟨fun ξ hξ h1 => ?_, fun f hf ξ hξ y hy z hz => ?_⟩
    · rw [Set.disjoint_left]
      intro z hz hzξ
      obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hzξ
      have hmem : ξ ∈ D.filter (fun ξ => ξ ≠ 1) := Finset.mem_filter.mpr ⟨hξ, h1⟩
      have hzC : ξ • v ∈ C ξ := (Set.mem_iInter₂.mp hz.1.2 ξ hmem).1
      have hvC : ξ • v ∈ (C ξ)ᶜ := (Set.mem_iInter₂.mp hv.1.2 ξ hmem).2
      exact hvC hzC
    · have hmem : (f, ξ) ∈ F ×ˢ B := Finset.mem_product.mpr ⟨hf, hξ⟩
      have h1 : f (ξ • y) = f (ξ • x) := Set.mem_iInter₂.mp hy.2 (f, ξ) hmem
      have h2 : f (ξ • z) = f (ξ • x) := Set.mem_iInter₂.mp hz.2 (f, ξ) hmem
      exact h1.trans h2.symm

/-- **tex l.157–159, as printed**: for a group acting topologically freely by homeomorphisms on a
totally separated space, every nonempty clopen set contains a nonempty small one. -/
def PrintedGeneralSmallSets : Prop :=
  ∀ (Λ Z : Type) [Group Λ] [TopologicalSpace Z] [TotallySeparatedSpace Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z], (∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) →
    ∀ (D B : Finset Λ) (F : Finset (LocallyConstant Z (ZMod 2))) (A : Set Z), IsClopen A →
      A.Nonempty → ∃ V : Set Z, IsClopen V ∧ V.Nonempty ∧ V ⊆ A ∧ IsSmall D B F V

theorem printedGeneralSmallSets : PrintedGeneralSmallSets :=
  fun _ _ _ _ _ _ _ hfree D B F _ hA hne => exists_isSmall_subset hfree D B F hA hne

end General
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.dense_moved
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.exists_isSmall_subset
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.General.printedGeneralSmallSets
