import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch4TransferNonzero
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferNonzero
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferAssembly
import Mathlib

/-!
# Branch 4 — Construct `TopHomologyTransferNonzeroWitness` (Prompt 55)

This file packages Prompt 54's nonzero-transfer theorem
`b4_RPToSphereTransferTopNonzero` into the exact homology-side witness structure
`TopHomologyTransferNonzeroWitness n` consumed by the previously-returned
Aristotle transfer assembly (`rpnTopClassTransfer_of_cellular_witness`), and then
derives the conditional Branch-4 top-class transfer result.

## The witness

`TopHomologyTransferNonzeroWitness n` (defined in
`RPnTopClassTransferNonzero.lean`) is the **Prop**

```text
∀ c : sphereCohomology n n, c ≠ 0 →
  ∃ z : homologyZMod2 (TopCat.of (RP n)) n,
    (kroneckerMap (TopCat.of (Sphere n)) n).hom c
        ((projTransferHomologyZMod2 n n).hom z) ≠ 0
```

i.e. for every nonzero top sphere class `c`, some `RPⁿ` top homology class pairs
nontrivially with `c` after the homology transfer.

Over `F₂` this witness is *equivalent* to the nonzero-transfer predicate
`RPToSphereTransferTopNonzero n` produced by Prompt 54: by the
transfer–Kronecker adjunction (`cohTransferZMod2_kronecker_adjunction`) the
pairing `⟨c, tr_* z⟩` equals `⟨tr c, z⟩`, and by injectivity of the Kronecker
classifier over `F₂` (`cohTransferZMod2_ne_zero_iff_kronecker`) the transferred
class `tr c` is nonzero iff its Kronecker functional is nonzero, i.e. iff some
`z` pairs nontrivially with it.  Hence Prompt 54's `RPToSphereTransferTopNonzero`
supplies the witness.

## Outcome

Branch 3 has *not* (yet) constructed an unconditional
`RPnCellularCochainStructure n`; every downstream consumer takes it as a
hypothesis, and the Prompt-54 transfer additionally needs the top data
`d : B4TopData n` and the sphere rank-one input `hsphere`.  We therefore deliver
**Outcome B**: the Branch-4 top-class transfer conditional on this honest data.
The bundled `d.cc : RPnCellularCochainStructure n` field supplies the cellular
input to the assembly.  Prompt 56 can remove the remaining hypotheses once
Branch 3 provides the unconditional cellular datum (and the sphere rank-one
computation) upstream.

No `axiom`, `sorry`, `opaque`, or `admit` is used.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **The homology-side witness, from Prompt 54.** Given the Prompt-53/54 top
data `d : B4TopData n` and one-dimensionality of `Hⁿ(Sⁿ; F₂)` (`hsphere`), the
homology-side residual `TopHomologyTransferNonzeroWitness n` holds: every nonzero
top sphere class pairs nontrivially with some `RPⁿ` top homology class after the
homology transfer.

The proof turns the Prompt-54 nonzero-transfer fact
`b4_RPToSphereTransferTopNonzero` into the witness via the Kronecker-injectivity
iff (`cohTransferZMod2_ne_zero_iff_kronecker`) and the transfer–Kronecker
adjunction (`cohTransferZMod2_kronecker_adjunction`). -/
theorem b4_topHomologyTransferNonzeroWitness (n : ℕ) (d : B4TopData n)
    (hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1) :
    TopHomologyTransferNonzeroWitness n := by
  intro c hc
  -- Prompt 54: the cohomology transfer of `c` is nonzero.
  have htr : (cohTransferZMod2 n n).hom c ≠ 0 :=
    b4_RPToSphereTransferTopNonzero n d hsphere c hc
  -- Over `F₂`, nonzero transfer means the Kronecker functional of `tr c` is nonzero.
  rw [cohTransferZMod2_ne_zero_iff_kronecker] at htr
  -- A nonzero functional takes a nonzero value on some homology class `z`.
  obtain ⟨z, hz⟩ :
      ∃ z : homologyZMod2 (TopCat.of (RP n)) n,
        (kroneckerMap (TopCat.of (RP n)) n).hom ((cohTransferZMod2 n n).hom c) z ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact htr (by ext z; simpa using hcon z)
  refine ⟨z, ?_⟩
  -- Transfer–Kronecker adjunction: `⟨c, tr_* z⟩ = ⟨tr c, z⟩ ≠ 0`.
  rw [← cohTransferZMod2_kronecker_adjunction]
  exact hz

/-- **Conditional Branch-4 top-class transfer (Outcome B).** From the honest
Prompt-54 data (`d : B4TopData n` and the sphere rank-one input `hsphere`) the
double-cover top-class transfer predicate `RPnTopClassTransfer n` holds.  The
cellular input to the assembly is the bundled `d.cc`, and the transfer input is
supplied through the homology-side witness `b4_topHomologyTransferNonzeroWitness`
and the Aristotle assembly `rpnTopClassTransfer_of_cellular_witness`. -/
theorem b4_RPnTopClassTransfer_of_cellular (n : ℕ) (d : B4TopData n)
    (hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1) :
    RPnTopClassTransfer n :=
  rpnTopClassTransfer_of_cellular_witness n d.cc
    (b4_topHomologyTransferNonzeroWitness n d hsphere)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

