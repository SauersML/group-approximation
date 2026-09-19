import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCyclic.Reduction
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCore.Endpoints

/-!
# The cyclic extension step for amenable groups

`non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership` (tex l. 1376--1378),
cyclic extension step. For a countable amenable group, `IsModelled ⊤` holds
(`TWWCore.isModelled_top_of_isAmenable`, Tikuisis--White--Winter with Tu's UCT theorem),
so every subgroup is modelled and the cyclic extension closure is immediate.
-/

namespace GroupApproximation.Full.TWWCyclic

/-- **Cyclic extension closure for countable amenable groups**
(`thm:fixed-radical-membership`, cyclic extension step). -/
theorem isCyclicExtensionClosed_isModelled {G : Type} [Group G] [Countable G]
    (h : GroupApproximation.Amenability.IsAmenable G) :
    TWW.IsCyclicExtensionClosed (TWW.IsModelled (G := G)) :=
  isCyclicExtensionClosed_isModelled_of_isModelled_top (TWWCore.isModelled_top_of_isAmenable h)

end GroupApproximation.Full.TWWCyclic
