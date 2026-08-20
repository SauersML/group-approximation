---
rg: 2
id: dimension-reported-clifford-table-halting-compiler
kind: claim
title: A halting output dimension activates a uniformly sound supercritical Clifford table
distinct_from:
  dimension-reported-schur-replica-halting-compiler: that activates replicated non-CE BCS predicate packets and then selects forbidden contexts; this uses only one elementary extraspecial Pauli group whose marked irreducibles already have exponential dimension.
  finite-bi-index-clifford-tape-presentation: that finitely presents a coherent infinite coset-indexed Clifford family and asks for uniform site recovery; this only asks a halting computation to activate one finite complete multiplication table of a reported size.
---

Construct a total computable machine-to-group compiler with universal
constants `delta>0`, `alpha<sqrt(2)` and

```text
0<epsilon<min(1/2,alpha/42)
```

satisfying `(DMK1)` and the following dimension-matched halting clause.  If
the source machine halts and outputs `D`, its finite control computes an `N`
with `(MCT3)`.  Every `D`-dimensional tuple for the compiled presentation with
relator defect below `delta` and marked distance above `alpha` must decode to
an all-pairs `epsilon`-homomorphism

```text
f:E_N->U(D)
```

whose central sign satisfies `(MCT1)`.  The marked Clifford-table theorem then
contradicts the choice of `N`, proving `(DMK2)` in dimension `D`.

Table activation and mark-to-sign transfer must have constants independent of
`D`, `N`, and the halting runtime.  If the source never halts, an exact model
must retain the marked word as a nonidentity.

## Attempts

- This removes every nonlinear-predicate issue from the diagonal route.  No
  non-CE BCS, forbidden-mass selection, Schur rank gate, or common carrier
  synchronization is needed.
- Slofstra-style quantitative Higman embedding can expose arbitrarily long
  finite Clifford windows, but its error modulus deteriorates with the window
  and therefore does not supply the universal `delta` here.
- Ordinary machine/HNN simulation activates the terminal table only through
  a derivation whose length depends on runtime; word telescoping has the same
  defect.
- The remaining task is a perfect-complete, constant-soundness compiler from
  a halting computation to the complete multiplication table of `E_N`.
  Recursive verifier compression is stronger than necessary but has the
  right runtime-independent quantitative shape.
- Natarajan--Vidick's Pauli braiding test (arXiv:1610.03574) is a smaller
  analytic substitute for the complete table: with Magic Square as its
  anticommutation test it has perfect completeness and robustness independent
  of `N`, uses `O(N)`-bit questions and constant-size answers, and self-tests
  `N` EPR pairs.  The remaining conversion is exact: turn those
  state-dependent multi-prover checks into normalized-HS group-word checks
  while preserving the dormant nonhalting model.  The question alphabet still
  grows with `N`, so this does not by itself perform the halting activation.
