---
rg: 2
id: zpc-frozen-equation-menu-has-positive-orbitwise-class
kind: claim
title: The perfect gap ZPC strategy has a positive orbitwise frozen equation-menu class
distinct_from:
  zpc-readable-control-freezing-to-lcs: that asks directly for a commuting LCS solution after freezing all readable bits; this asks only for one readable atom on whose entire unreadable orbit the finitely many equations selected at that atom remain valid.
  zpc-readable-variables-global-boolean-field: that constructs the finite measurable readable partition but gives no orbitwise invariance; this permits the partition labels to move whenever the selected frozen equation menu stays unchanged.
---

Let `G` and its perfect ZPC-IRS strategy be the witness from
`perfect-zpc-irs-quantum-gap-game`.  Let `p_r` be the atoms of its finite
global readable field.  For some `r` with positive measure, put

```text
P=p_r (1-J)/2.                                          (ZOM1)
```

The claim is that every defining unreadable commutator and every affine word
`w_(r,j)=J^(b_(r,j))` selected by the frozen assignment `r` has the same
scalar compression on every unreadable translate of `P`: for all unreadable
words `g`,

```text
P g^-1 w_(r,j) J^(-b_(r,j)) g P=P.                     (ZOM2)
```

Equivalently, the orbit of a positive part of one readable atom remains
inside the measurable class of points satisfying the entire equation menu
selected by `r`.  Remote readable coordinates may change along this orbit;
only verifier-relevant equation selection must remain constant.

This is strictly weaker than an invariant readable atom and is the exact
positive resource exposed by
`scalar-relator-compression-does-not-kill-normal-ideal`.  It remains open for
the non-halting perfect-gap witness.

## Attempts

- **Perfect acceptance stops at the base atom.**  It proves `(ZOM2)` for
  `g=1`.  After translating by an unreadable word, the readable assignment
  may change and perfect acceptance authenticates the menu selected at the
  translated point, not the original menu indexed by `r`.  This is exactly
  the normal-ideal sandwich exposed by the two-dimensional compression
  counterexample.
- **Finite menu classes need not contain an invariant component.**  Although
  only finitely many equation menus occur, an ergodic unreadable action may
  permute all of them transitively.  Averaging their projections gives the
  identity but supplies no positive projection supported in one class and
  invariant under the unreadable generators.
- **Cheapest positive attack.**  Inspect the fixed TailoredMIP verifier after
  quotienting readable assignments by equality of their selected affine
  menus.  If every unreadable generator preserves this coarser finite
  quotient—even though it moves remote raw bits—then every positive menu
  atom satisfies `(ZOM2)`.  No such verifier-specific preservation theorem is
  presently recorded.
