# STW XV: the solid-ring reduction for strongly self-absorbing K-theory

*2026-08-30 goal session.  Companion to
`stw99-problem-xv-ssa-k-theory-range`; establishes
`ssa-kunneth-forces-solid-k-theory` and the conditional route
`stw99-iv-implies-xv-torsion-free`.*

## The theorem in one line

SSA + Künneth-against-itself ⟹ `K_1 = 0` (unconditional via
Toms--Winter flip + Winter `Z`-stability + Jiang `K_1`-injectivity)
and `K_0` is a Bousfield--Kan SOLID ring (multiplication
`K_0 ⊗ K_0 → K_0` is bijective, being inverse to the first-factor
isomorphism `x ↦ x ⊗ [1]`).

## Why this is the right invariant-side closure

* Solid rings are classified (Bousfield--Kan 1972): localizations
  `Z[J^{-1}]`, cyclic `Z/n`, compatible products, colimits.  The
  torsion-free ones are exactly the localizations — precisely the
  `K_0`-range of the KNOWN strongly self-absorbing list.  So on the
  torsion-free locus, the invariant-side content of Problem XV is
  CLOSED modulo the Künneth problem IV; what remains of XV entirely
  concerns hypothetical SSA algebras with `K_0`-torsion in a solid
  pattern (`Z/n` or `Z[J^{-1}] × Z/n`), or Künneth failures (which
  would refute IV, a UCT-level event).
* FOLLOW-UP CLOSED (`embeddable-unit-class-non-torsion`): the
  ultrapower reindexing lemma shows any unitally
  `(Q ⊗ O_∞)_ω`-embeddable algebra has non-torsion unit class, so the
  pure cyclic solids `Z/n` (and `K_0 = 0`) are EXCLUDED for
  embeddable candidates; the XV residue is exactly the product solids
  `Z[J^{-1}] × Z/n`, whose unit `(1,1)` is non-torsion.  The same
  lemma shows the `O_2`-exclusion in Kirchberg's Problem XIV(2) is
  K-theoretically forced.
* Correction to the XV root's earlier Attempts: `K_1(D) = 0` is not
  merely "accessible" — it is unconditional literature (the cited
  chain); the node text is updated.

## Sanity models

`Z`, `O_∞` (`Z`); UHF `M_{J^∞}` and `⊗ O_∞` (`Z[J^{-1}]`); `Q`-types
(`Q`); `O_2` (zero ring) — the known list realizes exactly the
occurring torsion-free solids, and no known SSA algebra realizes a
torsion solid, as the theorem predicts if XV is true.
