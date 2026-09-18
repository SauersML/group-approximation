import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFree.Configuration
import GroupApproximation.Manuscript.NonMF.FournierFacioParagraph
import GroupApproximation.Algebra.ProductFinitePresentation
import Mathlib.SetTheory.Cardinal.Free

/-!
# The notes configuration from the Fournier-Facio data

`non_mf_group_notes.tex`, Theorem `thm:torsionfree`, l.2767-2775. The proof
starts from the group `G_0` of `[FFF, Section 2]` (F. Fournier-Facio,
arXiv:2608.02025 v2, §2). `G_0` contains a Kazhdan subgroup `Γ`, a stable
letter `t₁` and an embedded simple group `S' ≤ Γ` with
`t₁ Γ t₁⁻¹ ⊆ Γ` and `t₁⁻¹ S' t₁ ⊆ C_{G_0}(Γ)`.

The same package appears in `non_mf_groups_exist.tex`, l.835-843, as
`PrintedFournierFacioData`. That version has a core `Γ`, a letter `t` and a
simple factor `J` with `[Γ, J] = 1` and `tJt⁻¹ ≤ Γ`. The notes' `S'` is
`tJt⁻¹`, and then `t⁻¹ S' t = J` centralizes `Γ`.

* `notesConfigurationOfPrintedData` builds a
  `GroupApproximation.Full.NN07b.NotesConfiguration` from the data. It sets
  `S' := tJt⁻¹` and takes the noncommuting pair to be the `t`-conjugates of a
  noncommuting pair of `J`.
* `exists_notesConfiguration_of_printedData` is the existence statement for a
  finitely presented `G_0`: it yields a configuration whose group is finitely
  generated and acylindrically hyperbolic.

No hypothesis in this file stands in for a cited theorem. Every argument is a
concrete group, subgroup or element, together with properties of that object.
-/

namespace GroupApproximation.Full.NN07c

open scoped commutatorElement
open GroupApproximation.Manuscript.NonMF

/-- `thm:torsionfree` (`non_mf_group_notes.tex`, l.2767-2775), configuration
step: the Fournier-Facio package `(Γ, t, J)` of `non_mf_groups_exist.tex`
l.835-843 gives the notes configuration with `S' = tJt⁻¹`. -/
noncomputable def notesConfigurationOfPrintedData {G₀ : Type} [Group G₀] [Countable G₀]
    (htf : IsPowerTorsionFree G₀) (hT : HasKazhdanPropertyT.{0, 0} G₀)
    (F : PrintedFournierFacioData G₀) (hFT : HasKazhdanPropertyT.{0, 0} ↥F.core)
    (x y : ↥F.simpleFactor) (hxy : ¬ Commute x y) : NN07b.NotesConfiguration where
  G₀ := G₀
  group := ‹Group G₀›
  countable := ‹Countable G₀›
  torsionFree := htf
  kazhdan := hT
  Γ := F.core
  kazhdanΓ := hFT
  t := F.t
  compresses := F.conj_core_mem
  S := F.simpleFactor.map (MulAut.conj F.t).toMonoidHom
  simple := by
    haveI : IsSimpleGroup ↥F.simpleFactor := F.simple
    exact (Subgroup.equivMapOfInjective F.simpleFactor (MulAut.conj F.t).toMonoidHom
      (MulAut.conj F.t).injective).symm.isSimpleGroup
  S_le := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hs
    exact F.conj_simpleFactor_mem c hc
  centralizes := by
    intro s hs δ hδ
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hs
    have heq : F.t⁻¹ * ((MulAut.conj F.t).toMonoidHom c) * F.t = c := by
      show F.t⁻¹ * (F.t * c * F.t⁻¹) * F.t = c
      group
    rw [heq]
    exact F.simpleFactor_centralizes c hc δ hδ
  a := F.t * (x : G₀) * F.t⁻¹
  b := F.t * (y : G₀) * F.t⁻¹
  a_mem := Subgroup.mem_map.mpr ⟨(x : G₀), x.2, rfl⟩
  b_mem := Subgroup.mem_map.mpr ⟨(y : G₀), y.2, rfl⟩
  commutator_ne_one := by
    intro h
    apply hxy
    have hc : F.t * (x : G₀) * F.t⁻¹ * (F.t * (y : G₀) * F.t⁻¹) =
        F.t * (y : G₀) * F.t⁻¹ * (F.t * (x : G₀) * F.t⁻¹) :=
      (commutatorElement_eq_one_iff_commute.mp h).eq
    have hxy' : (x : G₀) * (y : G₀) = (y : G₀) * (x : G₀) := by
      calc (x : G₀) * (y : G₀)
          = F.t⁻¹ * (F.t * (x : G₀) * F.t⁻¹ * (F.t * (y : G₀) * F.t⁻¹)) * F.t := by group
        _ = F.t⁻¹ * (F.t * (y : G₀) * F.t⁻¹ * (F.t * (x : G₀) * F.t⁻¹)) * F.t :=
          congrArg (fun z => F.t⁻¹ * z * F.t) hc
        _ = (y : G₀) * (x : G₀) := by group
    show x * y = y * x
    exact Subtype.ext hxy'

/-- `thm:torsionfree` (`non_mf_group_notes.tex`, l.2767-2775): the notes
configuration exists over any finitely presented, torsion-free, Kazhdan,
acylindrically hyperbolic `G_0` that carries the Fournier-Facio package with a
Kazhdan core. `non_mf_groups_exist.tex` l.835-843 says every such `G_0` from
`[FFF, §2]` is acylindrically hyperbolic, by `[Hull, Corollary 7.4]`. -/
theorem exists_notesConfiguration_of_printedData {G₀ : Type} [Group G₀]
    [hfp : Group.IsFinitelyPresented G₀]
    (htf : IsPowerTorsionFree G₀) (hT : HasKazhdanPropertyT.{0, 0} G₀)
    (hacyl : TorsionFree.IsAcylindricallyHyperbolic G₀)
    (F : PrintedFournierFacioData G₀) (hFT : HasKazhdanPropertyT.{0, 0} ↥F.core) :
    ∃ C : NN07b.NotesConfiguration,
      Group.FG C.G₀ ∧ TorsionFree.IsAcylindricallyHyperbolic C.G₀ := by
  haveI : Countable G₀ := by
    obtain ⟨_, φ, hφ, -⟩ := hfp.out
    exact hφ.countable
  obtain ⟨x, y, hxy⟩ := F.nonabelian
  exact ⟨notesConfigurationOfPrintedData htf hT F hFT x y hxy,
    ProductFinitePresentation.fg_of_isFinitelyPresented G₀, hacyl⟩

end GroupApproximation.Full.NN07c
