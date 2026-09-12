---
rg: 2
id: algebraic-strong-atiyah-counterexample-exists
kind: claim
title: Some torsion-free group has an algebraic group-ring matrix with non-integral von Neumann kernel dimension
distinct_from:
  algebraic-strong-atiyah-for-all-torsion-free-groups: that is the universal positive statement over the algebraic numbers; this asks for one violating group and matrix, which would refute it and the root.
---

**OPEN.**  Exhibit a torsion-free group `G` and `A in M_(m,n)(Qbar[G])` with
`dim_(N(G)) ker(r_A)` not an integer.  This refutes
`algebraic-strong-atiyah-for-all-torsion-free-groups` and
`strong-atiyah-torsion-free`.

**Necessary shape.**
- `G` is outside every class for which Strong Atiyah is proved; the lists in
  `strong-atiyah-torsion-free` and
  `universal-torsion-free-hosts-not-sofic-or-locally-indicable` apply.
- If the determinant conjecture holds for the master tester `E`, a
  counterexample over any torsion-free `G` produces one over `E` itself
  (`algebraic-atiyah-and-determinant-one-group-tester`).
- If instead Strong Atiyah holds for `E`, a counterexample produces an integral
  matrix with Fuglede--Kadison determinant below `1` over a nonsofic subgroup
  of `E`; see `determinant-counterexample-from-atiyah-counterexample`.
- A nonzero zero divisor `ab = 0` in `Qbar[G]` is such a counterexample:
  `r_a` is nonzero with nonzero kernel, so its kernel dimension lies strictly
  between `0` and `1`.

## Attempts

* **Import an exotic L2-Betti value.**  Dead as recorded in attempt 6 of
  `strong-atiyah-torsion-free`: the known irrational constructions need
  torsion subgroups of unbounded order.
* **Twisted corners over a torsion-free quotient.**
  `agent-bloop-strong-atiyah-corner-quantization-obstruction` produces
  failure only for a central extension with 2-torsion, whose Strong Atiyah
  lattice is `(1/2)Z`.  It does not cross to a torsion-free group.
* **Nonsofic torsion-free groups.**  They are where the approximation proofs
  stop (`universal-torsion-free-hosts-not-sofic-or-locally-indicable`), but
  nonsoficity produces no matrix and no kernel projection.  No candidate
  matrix over the Fournier--Facio group has been computed.
* **Supports built from one compressor.**  *Dead unless `Gamma` already
  fails*.
  - If `t Gamma t^-1` is a proper subgroup of `Gamma`, then `<Gamma, t>` is
    an extension of a directed union of copies of `Gamma` by `Z`
    (`one-compressor-support-atiyah-reduces-to-base`).  The same holds for a
    left Ore compressor family with torsion-free elementary amenable quotient.
    So a matrix supported there has integral kernel dimensions whenever
    `Gamma` satisfies Strong Atiyah.
  - Every positive Fournier--Facio compressor word is of this kind, and the
    two letters admit no common left multiple.
  - A counterexample over a compression host therefore needs a non-Ore
    two-letter pattern.  Its normal closure contains amalgams of copies of
    `Gamma` along compressed Kazhdan edge groups.  Strong Atiyah permanence is
    known there only for finite edge groups (Sanchez-Peralta,
    arXiv:2409.12268v2).
* **Finite spectrum.**  *Dead* as a source of torsion-free counterexamples
  independent of the Kadison--Kaplansky problem.
  - If `A^* A` has finite spectrum, its kernel projection is a polynomial in
    `A^* A`, so it is a projection in `M_n(Qbar[G])`.
  - Its trace is rational by Zalesskii's theorem (see
    `finite-spectrum-integral-elements-obey-determinant`).  A non-integral
    value is a nontrivial idempotent trace, which refutes the
    Kadison--Kaplansky conjecture for `G`.
  - A counterexample not of that kind must have spectrum accumulating at `0`.
* **Percolation coins, as in the lamplighter constructions.**  *Dies* at
  torsion-freeness.  The Z/2 constructions multiply by the algebraic
  idempotents `(1 + a_x)/2` of rank `1/2`.
  - Over a torsion-free lamp group `L` that satisfies Strong Atiyah, the
    division closure `D(L)` is a skew field.  It has no idempotents except 0
    and 1, so a coin at fixed matrix size `1` does not exist.
  - Coins in `M_2(D(L))`, such as the rank-one kernel projection of
    `(1 - a, 1 - b)` over a free lamp group, commute across slots only after
    tensoring.  That forces the matrix size to grow with the number of sites.
  - Rational expressions in a fixed matrix size give no commuting independent
    family of non-integral-rank projections.  This is a recorded reason, not a
    theorem: no percolation mechanism over torsion-free lamps is known.
