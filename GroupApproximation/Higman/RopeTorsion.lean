import GroupApproximation.Higman.RopeTrick
import GroupApproximation.Higman.ChiodoReduction
import GroupApproximation.GroupTheory.HNNBrittonCyclic

/-!
# The rope group is torsion-free when its inputs are

Chiodo's Theorem 2.2 differs from Higman's theorem in one clause: it preserves
the set of torsion orders, so a torsion-free group goes to a torsion-free
finitely presented group.  This file shows that clause is *not* an extra
theorem about the rope trick --- it is exactly the demand that the benign
witness be torsion-free.

The rope group is
`RopeGroup w = (Γ × (F ⧸ N)) ∗_ψ e` with `Γ = K ∗_L t`,
so its torsion is controlled twice by the same permanence theorem, which this
repository proves: `HNNBritton.isPowerTorsionFree_hnn`.  Hence

    K torsion-free  and  F ⧸ N torsion-free   ⟹   RopeGroup torsion-free.

So `Higman.TorsionPreservation` --- Higman's theorem *with* Chiodo's clause ---
follows from a single refinement of `REBenign`: that the benign witness of a
recursively enumerable normal subgroup can be taken torsion-free.  That
refinement is `REBenignTF` below, and it replaces both `REBenign` and
`TorsionPreservation`.
-/

namespace GroupApproximation
namespace Higman

/-! ## 1.  The torsion of the rope group -/

variable {F : Type} [Group F] {N : Subgroup F} [N.Normal] (w : BenignWitness N)

/-- **The rope group is torsion-free when the witness and the quotient
are.** -/
theorem torsionFree_ropeGroup (hK : IsPowerTorsionFree w.K)
    (hT : IsPowerTorsionFree (F ⧸ N)) :
    IsPowerTorsionFree (Rope.RopeGroup w) := by
  have hGamma : IsPowerTorsionFree (Rope.Gamma w) :=
    HNNBritton.isPowerTorsionFree_hnn (MulEquiv.refl w.L) hK
  have hAmb : IsPowerTorsionFree (Rope.Amb w) :=
    IsPowerTorsionFree.prod hGamma hT
  exact HNNBritton.isPowerTorsionFree_hnn (Rope.psi w) hAmb

/-! ## 2.  Torsion-free benign witnesses -/

/-- A benign witness whose overgroup is torsion-free. -/
structure TorsionFreeBenignWitness {G : Type} [Group G] (H : Subgroup G) where
  /-- The witness. -/
  witness : BenignWitness H
  /-- Its overgroup is torsion-free. -/
  torsionFree : IsPowerTorsionFree witness.K

/-- **The rope trick with the torsion clause.**  A torsion-free benign witness
for `N` gives a finitely presented *torsion-free* group containing `F ⧸ N`. -/
theorem nonempty_hull_of_benignTF [Group.IsFinitelyPresented F] [Group.FG F]
    (u : TorsionFreeBenignWitness N) (hT : IsPowerTorsionFree (F ⧸ N)) :
    Nonempty (ChiodoHost.TorsionFreeHigmanHull (F ⧸ N)) := by
  obtain ⟨SF, hSF, hSFfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG F)
  letI : Group.IsFinitelyPresented (Rope.RopeGroup u.witness) :=
    Rope.isFinitelyPresented_ropeGroup u.witness SF hSFfin hSF
  exact ⟨{ Carrier := Rope.RopeGroup u.witness
           torsionFree := torsionFree_ropeGroup u.witness u.torsionFree hT
           emb := Rope.quotientEmb u.witness
           emb_injective := Rope.quotientEmb_injective u.witness }⟩

/-! ## 3.  The refined input, and what it replaces -/

/-- **Input: Higman's Sections 2--4, with Chiodo's torsion clause.**  A
recursively enumerable normal subgroup of a free group of finite rank has a
benign witness whose overgroup is torsion-free.

This is one statement, and it replaces two: it implies `REBenign` by
forgetting the torsion clause, and it implies `TorsionPreservation` through
the rope trick.

**Nothing inhabits this structure.** -/
structure REBenignTF where
  /-- Torsion-free benign witnesses for recursively enumerable normal
  subgroups. -/
  benign : ∀ (n : ℕ) (N : Subgroup (FreeGroup (Fin (n + 1)))), N.Normal →
    REPred (fun v : RawWord => rawToFree n v ∈ N) →
    Nonempty (TorsionFreeBenignWitness N)

/-- The refinement implies the plain statement. -/
theorem reBenign_of_reBenignTF (h : REBenignTF) : REBenign where
  benign := by
    intro n N hN hre
    obtain ⟨u⟩ := h.benign n N hN hre
    exact ⟨u.witness⟩

/-- **The refinement implies Higman's theorem with the torsion clause.** -/
theorem torsionPreservation_of_reBenignTF (h : REBenignTF) : TorsionPreservation where
  hull := by
    intro B _ p htf
    classical
    set F := FreeGroup (Fin (p.rank + 1)) with hF
    set M : Subgroup F := MonoidHom.ker p.π with hM
    have hre : REPred (fun v : RawWord => rawToFree p.rank v ∈ M) := by
      have hiff : (fun v : RawWord => rawToFree p.rank v ∈ M)
          = (fun v : RawWord => p.π (rawToFree p.rank v) = 1) := by
        funext v
        exact propext ⟨fun hv => MonoidHom.mem_ker.mp hv,
          fun hv => MonoidHom.mem_ker.mpr hv⟩
      rw [hiff]
      exact p.re
    obtain ⟨u⟩ := h.benign p.rank M (MonoidHom.normal_ker p.π) hre
    letI : Group.FG F := ProductFinitePresentation.fg_of_isFinitelyPresented F
    have hiso : F ⧸ M ≃* B :=
      QuotientGroup.quotientKerEquivOfSurjective p.π p.π_surjective
    have hTq : IsPowerTorsionFree (F ⧸ M) :=
      IsPowerTorsionFree.comap htf hiso.toMonoidHom hiso.injective
    obtain ⟨H⟩ := nonempty_hull_of_benignTF u hTq
    exact ⟨torsionFreeHigmanHullComp H hiso.symm.toMonoidHom hiso.symm.injective⟩

end Higman
end GroupApproximation
