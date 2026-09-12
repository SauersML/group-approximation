# STW XV: the solid-ring reduction for strongly self-absorbing K-theory

*2026-08-30 goal session.  Companion to
`stw99-problem-xv-ssa-k-theory-range`; establishes
`ssa-kunneth-forces-solid-k-theory` and the conditional route
`stw99-iv-implies-xv-torsion-free`.*

## The theorem in one line

SSA + Künneth-against-itself ⟹ `K_1 = 0` (by the graded
unit-insertion isomorphism; this is conditional on self-Künneth)
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
* Correction (2026-08-31): automatic `K_1`-injectivity of SSA algebras
  is not `K_1`-vanishing. Toms--Winter derive `K_1(D)=0` under the
  UCT/Kunneth hypothesis. The theorem here remains valid because
  self-Kunneth itself forces the graded unit-insertion map to be an
  isomorphism and hence forces `K_1(D)=0`.

## Sanity models

`Z`, `O_∞` (`Z`); UHF `M_{J^∞}` and `⊗ O_∞` (`Z[J^{-1}]`); `Q`-types
(`Q`); `O_2` (zero ring) — the known list realizes exactly the
occurring torsion-free solids, and no known SSA algebra realizes a
torsion solid, as the theorem predicts if XV is true.


## Upgrade (same day, later): torsion-freeness is automatic — XV closes modulo self-Künneth

The degree-ONE Künneth sequence was left unused in the first pass.
With `K_1(D) = 0` its tensor part vanishes, so
`K_1(D ⊗ D) ≅ Tor(K_0, K_0)`; the first-factor isomorphism kills it,
and `Tor(A, A) = 0` means `A` is torsion-free.  So the product solids
`Z[J^{-1}] × Z/n` — the residue left by the unit-torsion lemma — are
DEAD as well: every strongly self-absorbing algebra satisfying the
Künneth sequence against itself has `K`-theory `(Z[J^{-1}], 0)` or
`(0, 0)`, i.e. the `K`-theory of a known strongly self-absorbing
algebra.  **STW Problem XV is closed in full modulo the single
hypothesis of self-Künneth**, and a counterexample must violate the
Künneth sequence for the pair `(D, D)` — a UCT-level event.  In the
`K = 0` case the XVI reference theorem upgrades to `D ≅ O_2`.

Downstream consolidation for XIII (the known-list problem): modulo
self-Künneth, a strongly self-absorbing `D` has the ordered
`K`-theory of a known `E`, and the XVI machinery then reduces
`D ≅ E` to (i) embeddability (Problem XIV(2)) and (ii) the
`J`-adapted-model wall for proper-`J` UHF targets and `Z`/`O_∞`.  So
XIII factors as: self-Künneth + XIV(2) + `J`-adapted models — three
named residues, each strictly weaker than the UCT.
