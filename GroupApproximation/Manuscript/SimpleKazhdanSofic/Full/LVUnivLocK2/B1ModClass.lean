import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.LinearAlgebra.Prod

/-!
# Exact categories of modules (lane LVUnivLocK2-B1)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii, input W1.
Quillen's localization and dévissage theorems (Quillen 1973 §§5-6) are statements about
exact categories.  All exact categories needed for W1 are full subcategories of `R`-modules,
closed under extensions and containing `0`, with the short exact sequences of modules as
conflations:

* `P(R)`: finitely generated projective modules (`ModClass.fgProj`);
* the torsion category `T_Σ` of a universal localization (finitely presented modules of
  projective dimension `≤ 1` killed by `Σ⁻¹R ⊗ -`), and the finite-length categories of
  dévissage.

`ModClass R` is this notion: a predicate on `ModuleCat R`, invariant under isomorphism,
containing the zero modules, and closed under extensions.  Conflations are triples
`f : M' → M`, `g : M → M''` with `f` injective, `g` surjective and `Function.Exact f g`.
The `K`-groups of such a class are in `B1K1`.
-/

namespace GroupApproximation.Full.LVUnivLocK2

universe u v

/-- **An extension-closed class of `R`-modules** (an exact category of modules, conflations the
short exact sequences).  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
structure ModClass (R : Type u) [Ring R] where
  /-- Membership of a module in the class. -/
  mem : ModuleCat.{v} R → Prop
  /-- The class is invariant under isomorphism. -/
  mem_of_equiv : ∀ {M N : ModuleCat.{v} R}, (M ≃ₗ[R] N) → mem M → mem N
  /-- The class contains the zero modules. -/
  mem_of_subsingleton : ∀ M : ModuleCat.{v} R, Subsingleton M → mem M
  /-- The class is closed under extensions. -/
  mem_of_exact : ∀ {M N P : ModuleCat.{v} R} (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Injective f → Function.Surjective g → Function.Exact f g →
      mem M → mem P → mem N

namespace ModClass

variable {R : Type u} [Ring R]

/-- The objects of the exact category. -/
abbrev Obj (C : ModClass.{u, v} R) := {M : ModuleCat.{v} R // C.mem M}

/-- The canonical zero object `PUnit`. -/
def zeroObj (C : ModClass.{u, v} R) : C.Obj :=
  ⟨ModuleCat.of R PUnit.{v + 1}, C.mem_of_subsingleton _ (inferInstanceAs (Subsingleton PUnit))⟩

instance subsingleton_zeroObj (C : ModClass.{u, v} R) : Subsingleton (C.zeroObj.1 : Type v) :=
  inferInstanceAs (Subsingleton PUnit)

/-- A class is closed under finite direct sums.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem mem_prod (C : ModClass.{u, v} R) {M N : ModuleCat.{v} R} (hM : C.mem M) (hN : C.mem N) :
    C.mem (ModuleCat.of R (M × N)) :=
  C.mem_of_exact (M := M) (P := N) (LinearMap.inl R M N) (LinearMap.snd R M N)
    LinearMap.inl_injective LinearMap.snd_surjective Function.Exact.inl_snd hM hN

/-- An isomorphism `e : M ≃ N` with `0` is a conflation `M ↣ N ↠ 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exact_equiv_zero (C : ModClass.{u, v} R) {M N : ModuleCat.{v} R} (e : M ≃ₗ[R] N) :
    Function.Exact e.toLinearMap (0 : N →ₗ[R] C.zeroObj.1) := fun y =>
  ⟨fun _ => ⟨e.symm y, e.apply_symm_apply y⟩, fun _ => Subsingleton.elim _ _⟩

/-- The map to the zero object is onto.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem surjective_zero (C : ModClass.{u, v} R) (N : ModuleCat.{v} R) :
    Function.Surjective (0 : N →ₗ[R] C.zeroObj.1) := fun _ => ⟨0, Subsingleton.elim _ _⟩

/-- A middle term of a conflation of finitely generated projective modules is finitely
generated projective (the conflation splits).  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem finite_projective_of_exact {M N P : Type v} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM : Module.Finite R M ∧ Module.Projective R M)
    (hP : Module.Finite R P ∧ Module.Projective R P) :
    Module.Finite R N ∧ Module.Projective R N := by
  have := hM.1
  have := hM.2
  have := hP.1
  have := hP.2
  obtain ⟨l, hl⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)
  have e := (hfg.splitSurjectiveEquiv hf ⟨l, hl⟩).1
  exact ⟨Module.Finite.of_exact hfg hg, Module.Projective.of_equiv' e.symm⟩

/-- **The exact category `P(R)` of finitely generated projective `R`-modules.**
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def fgProj (R : Type u) [Ring R] : ModClass.{u, v} R where
  mem M := Module.Finite R M ∧ Module.Projective R M
  mem_of_equiv e h := by
    have := h.1
    have := h.2
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv' e⟩
  mem_of_subsingleton _ hM := by
    have := hM
    exact ⟨inferInstance, inferInstance⟩
  mem_of_exact f g hf hg hfg hM hP := finite_projective_of_exact f g hf hg hfg hM hP

theorem mem_fgProj {M : ModuleCat.{v} R} :
    (fgProj.{u, v} R).mem M ↔ Module.Finite R M ∧ Module.Projective R M :=
  Iff.rfl

end ModClass

end GroupApproximation.Full.LVUnivLocK2
