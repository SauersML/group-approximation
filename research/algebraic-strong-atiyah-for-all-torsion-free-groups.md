---
rg: 2
id: algebraic-strong-atiyah-for-all-torsion-free-groups
kind: claim
title: Every torsion-free group satisfies Strong Atiyah over the algebraic numbers
refuted_by:
  - algebraic-strong-atiyah-counterexample-exists
distinct_from:
  strong-atiyah-torsion-free: that is the conjecture over the complex numbers; this is the algebraic-coefficient case, which it implies, and where the determinant conjecture supplies colimit permanence.
---

**OPEN.**  For every torsion-free group `G` and every
`A in M_(m,n)(Qbar[G])`, `dim_(N(G)) ker(r_A)` is an integer.  Taking
`K = Qbar` in the root, this is implied by `strong-atiyah-torsion-free`, and
it implies the characteristic-zero zero-divisor conjecture over `Qbar`.

## Attempts

* **Through the master host.**  `algebraic-strong-atiyah-via-master-host`
  derives this claim from Strong Atiyah and the determinant conjecture for the
  single group `E`, using the new colimit permanence
  `algebraic-atiyah-with-determinant-closed-under-colimits`.  Both inputs are
  open, and the standard proofs of each die at the host
  (`universal-torsion-free-hosts-not-sofic-or-locally-indicable`).
* **Without the determinant conjecture.**  Along directed colimits only the
  upper bound `dim ker r_A >= limsup_j dim ker r_(A_j)` is available, and
  small positive spectrum of the stages can become a fractional atom.  No
  replacement for the determinant bound is known; by consequence 2 of
  `algebraic-atiyah-and-determinant-one-group-tester`, a counterexample here,
  given Strong Atiyah for `E`, is exactly a determinant failure at a nonsofic
  subgroup of `E`.
