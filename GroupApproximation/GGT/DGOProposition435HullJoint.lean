import GroupApproximation.GGT.DGOProposition435
import GroupApproximation.GGT.HullSCLemma44FamilyInclusionStatement
import GroupApproximation.GGT.HullSCFillingSelectionTheorem316
import GroupApproximation.GGT.DGOProposition435InclusionFinite

/-!
# The joint peripheral family of Hull's Lemma 4.4, from Proposition 4.35

`HullSC.JointAuxiliaryPeripheralEmbedding` is the input the repaired
Lemma 4.4 statement binds: for a selected auxiliary family and an original
hyperbolically embedded family, a *joint* hyperbolically embedded family over
the sum index.  This module proves it from
`GGT.RelHyp.DGOProposition435InclusionStatement`, and with it flips the
unrepaired family-inclusion leaf.

## Why the nested form is the one that applies

`AuxiliaryPeripheralFamily.base_le` gives only
`A.alphabet.carrier ⊆ selected.rel.base`, because `adjoinPair` adds the target
letters and Osin's Theorem 5.4 then enlarges the base further; and the
hypothesis of the joint-selection input gives only
`original.alphabet.carrier ⊆ A.alphabet.carrier`.  Composing them is exactly
`original.alphabet.carrier ⊆ selected.rel.base`, the hypothesis of the nested
form.  The joint family is `GGT.RelHyp.jointRelGenSet`, whose base is the
proper part of the original relative base, the base letters that are not
already peripheral letters.  That base is inversion-closed, which the joint
interface demands and a bare `GGT.RelGenSet` does not supply, and dropping
those letters leaves the alphabet unchanged because they come back as
peripheral letters of the sum.

The nested form has two residues, the hyperbolicity of the joint Cayley graph
and the local finiteness of the original peripheral metrics.  The first is
discharged whenever Hull's alphabet is the original relative alphabet:
`jointHyperbolic_of_selection_at_hullAlphabet` does that from the base
equality that the selection producer records, and
`exists_selection_jointHyperbolic_of_finiteYi` runs the producer to get it
from Hull's `yi` statement alone.  So at a matched alphabet only the local
finiteness of the original family is left, which is the single residue of the
equal-alphabet form.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The joint-selection input -/

/-- **The joint-family selection input, from Proposition 4.35's nested
form.**

The joint family is the labelled sum of the original family and the selected
auxiliary family over the proper part of the original relative base.  Its base
is inversion-closed, it restricts to the original family on the left and to the
selected auxiliary peripherals on the right, and the nested form of
Proposition 4.35 makes it hyperbolically embedded. -/
theorem jointAuxiliaryPeripheralEmbedding_of_dgoProposition435Inclusion
    (h435 : GGT.RelHyp.DGOProposition435InclusionStatement.{u, w, 0}) :
    JointAuxiliaryPeripheralEmbedding.{u, w} := by
  intro G _ A N k S selected Lambda original hA horig
  have hbase : original.alphabet.carrier ⊆ selected.rel.base :=
    hA.trans selected.base_le
  exact ⟨GGT.RelHyp.jointRelGenSet original selected.rel,
    GGT.RelHyp.jointRelGenSet_base_inv original selected.rel,
    fun _ => rfl, fun i => selected.fam_eq i,
    h435 original selected.rel hbase horig selected.embedded,
    ⟨∅, Set.finite_empty,
      Set.subset_union_of_subset_left (GGT.RelHyp.properBase_subset_base original) ∅⟩⟩

/-- **The joint-family selection input, from the finite nested form.**  The
selected auxiliary family is indexed by a finite type and its relative base is
closed under inversion, which is what the finite form asks. -/
theorem jointAuxiliaryPeripheralEmbedding_of_dgoProposition435InclusionFinite
    (h435 : GGT.RelHyp.DGOProposition435InclusionFiniteStatement.{u, w, 0}) :
    JointAuxiliaryPeripheralEmbedding.{u, w} := by
  intro G _ A N k S selected Lambda original hA horig
  have hbase : original.alphabet.carrier ⊆ selected.rel.base :=
    hA.trans selected.base_le
  exact ⟨GGT.RelHyp.jointRelGenSet original selected.rel,
    GGT.RelHyp.jointRelGenSet_base_inv original selected.rel,
    fun _ => rfl, fun i => selected.fam_eq i,
    h435 original selected.rel hbase selected.base_inv horig selected.embedded,
    ⟨∅, Set.finite_empty,
      Set.subset_union_of_subset_left (GGT.RelHyp.properBase_subset_base original) ∅⟩⟩

/-- **The three conditions the relator re-spelling puts on the joint family**,
all met by the auxiliary-alphabet form.

The re-spelling is an index relabelling of one relative alphabet, so it needs
the joint base inside the selected base, the two alphabets equal, and the
adjoined filling target among the joint base letters.  The last one needs the
target to avoid every original peripheral, since a peripheral element cannot be
a base letter of a hyperbolically embedded family. -/
theorem jointRelGenSetFull_respelling_inputs
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    {t : G} (ht : t⁻¹ ∈ selected.rel.base)
    (htn : ∀ lam : Lambda, t⁻¹ ∉ original.fam lam) :
    (GGT.RelHyp.jointRelGenSetFull original selected.rel).base ⊆
        selected.rel.base ∧
      (GGT.RelHyp.jointRelGenSetFull original selected.rel).alphabet.carrier =
          selected.rel.alphabet.carrier ∧
        t⁻¹ ∈ (GGT.RelHyp.jointRelGenSetFull original selected.rel).base :=
  ⟨GGT.RelHyp.jointRelGenSetFull_base_subset original selected.rel,
    GGT.RelHyp.jointRelGenSetFull_alphabet_carrier original selected.rel
      (hA.trans selected.base_le),
    GGT.RelHyp.jointRelGenSetFull_mem_base original selected.rel ht htn⟩

/-! ## The leaf flip -/

/-- **The unrepaired family-inclusion leaf, from the repaired joint leaf.**

`hullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint` needs the
joint-selection input, and Proposition 4.35's nested form supplies it.  So
every consumer of the unrepaired leaf keeps its current call shape, and the
two inputs it now rests on are the repaired Lemma 4.4 and Proposition 4.35. -/
theorem hullLemma44CanonicalQuotientFamilyInclusionStatement_of_dgo435
    (h435 : GGT.RelHyp.DGOProposition435InclusionStatement.{u, w, 0})
    (h44 : HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, w}) :
    HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, w} :=
  hullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint
    (jointAuxiliaryPeripheralEmbedding_of_dgoProposition435Inclusion h435) h44

/-- **The unrepaired family-inclusion leaf, from the finite nested form.** -/
theorem hullLemma44CanonicalQuotientFamilyInclusionStatement_of_dgo435Finite
    (h435 : GGT.RelHyp.DGOProposition435InclusionFiniteStatement.{u, w, 0})
    (h44 : HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, w}) :
    HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, w} :=
  hullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint
    (jointAuxiliaryPeripheralEmbedding_of_dgoProposition435InclusionFinite h435)
    h44

/-! ## Discharging the hyperbolicity residue at a matched alphabet -/

/-- **At a matched Hull alphabet the first residue of the nested form is
free.**

If the selected auxiliary family is coned off over Hull's alphabet itself and
the original relative alphabet *is* Hull's alphabet, then the joint alphabet
equals the auxiliary one and its Cayley graph is the auxiliary Cayley graph.
Only the local finiteness of the original peripheral metrics is then left. -/
theorem jointHyperbolic_of_selection_at_hullAlphabet
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    (hselbase : selected.rel.base = A.alphabet.carrier)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (hA : original.alphabet.carrier = A.alphabet.carrier) :
    ∃ delta : ℝ, IsHyperbolicSpace delta
      (Cayley (GGT.RelHyp.jointRelGenSet original selected.rel).alphabet) :=
  GGT.RelHyp.dgoProposition435JointHyperbolic_of_base_eq original selected.rel
    (by rw [hselbase, hA]) selected.embedded

/-- **The enlargement of the auxiliary base is irrelevant to the residue.**

The joint alphabet is the original relative alphabet together with the selected
peripherals; it never sees the auxiliary *base*.  So the hyperbolicity of the
joint Cayley graph can be borrowed from any auxiliary family with the same
peripherals, in particular from the one built by coning off Hull's alphabet
itself, before the filling target is adjoined and before Osin's Theorem 5.4
enlarges the base.  Only the gap between the original relative alphabet and
Hull's alphabet has to be finite, and it is empty at a matched alphabet.

This is what removes Osin's Theorem 5.4 from the residue entirely: the
enlargement is the price of Hull's Lemma 4.9, and Lemma 4.9 is not involved
here. -/
theorem jointHyperbolic_of_matched_peripherals
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected pre : AuxiliaryPeripheralFamily A N S)
    (hcores : ∀ i : AuxiliaryPeripheralIndex k,
      selected.cores.peripheral i = pre.cores.peripheral i)
    (hprebase : pre.rel.base = A.alphabet.carrier)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (hsub : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (hfin : (A.alphabet.carrier \ original.alphabet.carrier).Finite) :
    ∃ delta : ℝ, IsHyperbolicSpace delta
      (Cayley (GGT.RelHyp.jointRelGenSet original selected.rel).alphabet) := by
  have hfam : pre.rel.fam = selected.rel.fam := by
    funext i
    rw [pre.fam_eq i, ← hcores i, selected.fam_eq i]
  have hbase : original.alphabet.carrier ⊆ pre.rel.base := by
    intro x hx
    rw [hprebase]
    exact hsub hx
  have hfin' : (pre.rel.base \ original.alphabet.carrier).Finite := by
    rw [hprebase]
    exact hfin
  exact GGT.RelHyp.jointHyperbolic_of_finite_base_excess original selected.rel
    pre.rel hfam hbase hfin' pre.embedded.hyperbolic

/-- **Hull's `yi` statement already supplies the matched auxiliary family.**

The finite-family `yi` statement and the proved Theorem 3.16 assembly build the
auxiliary family by coning off Hull's alphabet itself, so its base is
`A.alphabet.carrier` on the nose; with the original relative alphabet equal to
that alphabet, the joint Cayley graph is hyperbolic with no further input. -/
theorem exists_selection_jointHyperbolic_of_finiteYi
    (hyi : YiSuitableFiniteFamily.{u})
    {G : Type u} [Group G] (A : HullGeneratingSet G) {N : Subgroup G}
    {k : ℕ} (S : Fin k → Subgroup G) (hN : Suitable A.alphabet N)
    (hS : ∀ j : Fin k, Suitable A.alphabet (S j))
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (hA : original.alphabet.carrier = A.alphabet.carrier) :
    ∃ selected : AuxiliaryPeripheralFamily A N S,
      ∃ delta : ℝ, IsHyperbolicSpace delta
        (Cayley (GGT.RelHyp.jointRelGenSet original selected.rel).alphabet) := by
  obtain ⟨selected, hselbase⟩ :=
    simultaneousAuxiliaryPeripheralSelectionAtHullAlphabet_of_finiteYi_theorem316
      hyi A S hN hS
  exact ⟨selected,
    jointHyperbolic_of_selection_at_hullAlphabet selected hselbase original hA⟩

end HullSC
end GroupApproximation
