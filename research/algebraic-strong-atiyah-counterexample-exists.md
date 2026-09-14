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
