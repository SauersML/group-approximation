import GroupApproximation.Higman.AbsorberProgram
import GroupApproximation.Higman.BridgePresentation
import GroupApproximation.Higman.CurrentREBenign

/-!
# Chiodo's Theorem 3.10 from Higman's ω-closure

`Sofic.ChiodoBelegradekTheorem` writes Chiodo Theorem 3.10 (= Belegradek
Theorem A.1) as the closed formula `ChiodoBelegradek.Statement` and proves two
of its three clauses unconditionally; the clause left over is finite
presentation, and `Higman.Program` prices it as Higman's embedding theorem in
Chiodo's torsion-order preserving form, his Theorem 2.2.

Everything that pricing itemized has since been discharged except one
construction, so Theorem 3.10 now stands on `Higman.Omega.OmegaInput` alone —
Higman's ω-closure, the three-stage tower proving that `ωₘ` preserves
benignness.  `chiodo_of_omega` is that composite, and it is the first
declaration in the repository to conclude `ChiodoBelegradek.Statement` from a
single hypothesis rather than from a packaged citation.

## The chain

| step | declaration |
| --- | --- |
| torsion-free benign witnesses for r.e. normal subgroups | `Higman.reBenignTF_of_omega` |
| the rope trick, turning those into finitely presented torsion-free hulls | `Higman.torsionPreservation_of_reBenignTF` |
| the repaired Higman--Neumann--Neumann bridge, unconditional | `Higman.BridgePresentation.bridgeEffective` |
| … carrying a countably generated recursive presentation into a finitely generated one | `Higman.BridgeEff.countableToFG_of_effective` |
| bridge with torsion clause = Chiodo Theorem 2.2 | `Higman.torsionFreeHigmanEmbedding_of_inputs` |
| Theorem 2.2 at the recursively presented absorber = Theorem 3.10 | `Higman.statement_of_higman` |

Two of the inputs `Higman.Program` lists are no longer hypotheses.  Chiodo's
Proposition 3.8 at the absorber is `Higman.recursivePresentationPCAbsorberFull`,
which `Higman.statement_of_higman` applies for itself; and the effectivity
clause of the bridge is `Higman.BridgePresentation.bridgeEffective`, proved from
the presentation of the three-generator HNN extension over its base.  Of the
three factors of `Higman.REBenignTF`, two — `Higman.higmanTheoremThree` and
`Higman.PairedReturnCutter.transportSectionFive` — are unconditional, and
`Higman.operationClosures_of_omega` reduces the third to the ω-closure.

So the hypothesis of `chiodo_of_omega` is the whole of what Theorem 3.10 is
owed here, and the group it produces is a rope group over a torsion-free
benign witness for the universal torsion-free quotient of `Higman.PCDirectSum`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TheoremC

/-- **Chiodo, arXiv:1107.1489v4, Theorem 3.10 (= Belegradek, Theorem A.1),
from Higman's ω-closure.**

> There exists a finitely presented torsion-free group containing a copy of
> every finitely presented torsion-free group.

The hypothesis is the sole remaining construction of the benign-subgroup route
to Higman's embedding theorem.  This discharges the `chiodo` field of
`TheoremC.LiteratureInputs` up to that one construction, which the recognition
lane already carries as a debt of its own. -/
theorem chiodo_of_omega (hOmega : Higman.Omega.OmegaInput) :
    ChiodoBelegradek.Statement :=
  Higman.statement_of_higman
    (Higman.torsionFreeHigmanEmbedding_of_inputs
      (Higman.BridgeEff.countableToFG_of_effective
        Higman.BridgePresentation.bridgeEffective)
      (Higman.torsionPreservation_of_reBenignTF (Higman.reBenignTF_of_omega hOmega)))

/-- The universal host of `Sofic.FournierFacioUniversalGroup`, from the same
hypothesis: the packaged form of the same theorem, so that consumers written
against the host rather than against the formula are served too. -/
theorem nonempty_universalTorsionFreeHost_of_omega
    (hOmega : Higman.Omega.OmegaInput) :
    Nonempty FournierFacioUniversal.UniversalTorsionFreeHost :=
  Higman.nonempty_host_of_higman
    (Higman.torsionFreeHigmanEmbedding_of_inputs
      (Higman.BridgeEff.countableToFG_of_effective
        Higman.BridgePresentation.bridgeEffective)
      (Higman.torsionPreservation_of_reBenignTF (Higman.reBenignTF_of_omega hOmega)))

end TheoremC
end NonMF
end Manuscript
end GroupApproximation
