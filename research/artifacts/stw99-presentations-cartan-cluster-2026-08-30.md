# STW XL--XLIX presentations and Cartan cluster audit (2026-08-30)

## Scope

This artifact records the first-pass decomposition of STW Problems XL--XLIX.
The ten roots split into three connected blocks:

1. amenable actions and crossed-product regularization (XL--XLII);
2. groupoid and transformation-group presentations (XLIII--XLVI);
3. Cartan recognition, classification, and relative Gamma (XLVII--XLIX).

No open root in this cluster is declared solved here.  The point of the
decomposition is to separate an established obstruction from the remaining
range and coherence questions.

## XL: the invariant-trace obstruction

The claim `amenable-action-invariant-trace-forces-amenability` is established
by `amenable-action-invariant-trace-amenability-proof`.  If an amenable action
of a countable group on a unital nuclear algebra preserved a trace, the
reduced crossed product would be nuclear and its induced trace would restrict
to the canonical trace on the reduced group algebra.  Passing to the finite
GNS von Neumann algebra and then through the trace-preserving expectation
onto the group von Neumann algebra would make `L(G)` injective.  Hence `G`
would be amenable.

Therefore a witness for Problem XL for a nonamenable exact group cannot fix
a trace.  It cannot even preserve a probability measure on `T(A)`, since the
barycenter would be an invariant trace.  Finite extremal trace boundaries are
excluded.  The remaining construction problem is an amenable action on a
stably finite classifiable algebra whose trace simplex supports genuinely
measure-fixed-point-free affine dynamics; a Poulsen-type trace simplex is the
natural unrestricted test case.

## XLI--XLII: regularization and invariant computation

Problem XLI asks when dynamics erase the non-`Z`-stable obstruction of the
base algebra.  The concrete test proposed in the root is orbitwise absorption
of comparison/perforation witnesses in `Cu(A)`, particularly for shifts on
Villadsen-type coordinate systems.  This is a test program, not an asserted
characterization.

Problem XLII asks to compute the Elliott invariant of crossed products over
already classifiable noncommutative bases.  Its additional obstruction beyond
the commutative problem is trace extension: one needs hypotheses ensuring
that every crossed-product trace is an invariant trace on the base composed
with the canonical expectation.  Strong outerness supplies this in several
controlled trace-boundary regimes, but the wild-boundary gluing statement
remains open.

## XLIII--XLVI: presentation range problems

The four presentation questions form a strict hierarchy of model classes:

```text
transformation-group model  =>  untwisted etale groupoid model
                            =>  twisted Cartan/groupoid model.
```

Known twisted groupoid range theorems do not automatically remove the twist.
The open XLIII cell combines torsion in `K_0` with unrestricted trace spaces;
the known untwisted orbit-breaking models and the general twisted models
control complementary halves of that data.

For XLIV, stabilization removes the order-unit bookkeeping, but exact
realization of the trace pairing by an amenable transformation group remains
the missing range theorem.  XLV restores the unit and therefore adds genuine
Pimsner--Voiculescu and positive-cone constraints.  XLVI is already closed in
the stable setting by the tensor-crossed-product trick recorded in its root;
its unresolved content is unital, where the same order-unit constraints as
XLV reappear.

## XLVII--XLIX: Cartan frontiers

Problem XLVII is kept in its sharp diagonal form.  Existing non-AF Cantor
Cartans in AF algebras have isotropy and therefore do not refute the proposed
principality/unique-extension criterion.  The positive hinge is whether a
principal etale groupoid with AF C-star algebra must itself be an AF
equivalence relation.

Problem XLVIII is encoded as a Borel-complexity question.  The missing input
is a conjugacy invariant capable of separating a turbulent family of Cantor
Cartans inside one fixed AF algebra; the currently visible groupoid and
homological invariants are countable-valued.

Problem XLIX compares relative uniform Gamma for two Cartans in one nuclear
algebra.  Its explicit candidate route uses a dynamical Cartan without the
small-boundary property and seeks a second Cartan with relative Gamma in the
same ambient algebra.  This remains contingent on the uniform-Gamma and
Cartan-transport nodes cited in the root.

## Integrity boundary

The artifact supports the cluster roots as a shared status ledger.  It does
not upgrade speculative attempts to theorems.  The only unconditional new
result recorded here is the invariant-trace obstruction for Problem XL; all
other bullets identify exact open interfaces or already stated stable-case
reductions.
