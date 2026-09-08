---
rg: 2
id: central-quotients-of-residually-finite-groups-are-mf
kind: claim
title: Every central quotient of a countable residually finite group is MF
distinct_from:
  abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center: that exhibits one central quotient of a linear group whose central mark dies in every EXACT finite-dimensional representation while surviving in permutation microstates; this proves the general positive statement for approximate representations, so it supplies the visible half for that calibration rather than contradicting its invisible half.
  invariant-graph-clifford-phase: that compares sofic radicals of invariant-graph central quotients up to a sign; this is an unconditional MF statement for arbitrary central quotients of arbitrary countable residually finite groups, with no graph or phase structure.
  mf-group-with-finite-central-compression-defect: that exhibits an MF group retaining a finite central subgroup inside the compression defect of an infinite cyclic subgroup; this is a construction of MF models for a whole class of groups and says nothing about which defects survive.
artifacts:
  - research/artifacts/central-quotient-rf-exclusion-2026-09-08.md
---

**ESTABLISHED.**  Let `Lambda` be a countable residually finite group, let
`Z <= Z(Lambda)`, and put `G = Lambda/Z`.  Then for every `g != 1` in `G`
there are `d_n` and maps `V_n : G -> U(d_n)` with `V_n(1) = I`,

```text
||V_n(xy) - V_n(x)V_n(y)|| -> 0   for all x,y in G,
liminf_n ||V_n(g) - I||_2 > 0,                                    (CQ1)
```
the sequence being allowed to depend on `g`.  Consequently

```text
G is MF.                                                          (CQ2)
```

There is **no** finite generation, torsion or finite-rank hypothesis on
`Z`: an infinitely generated central subgroup does not escape the
conclusion.

The mechanism is approximation of central characters in finite quotients.
Writing `C = Z(Lambda)`, every character `chi` of `C` is a pointwise limit
of central characters of finite-dimensional representations of `Lambda`
that factor through finite quotients; picking `chi` trivial on `Z` and
nontrivial at a prescribed `c` handles the elements of `C/Z`, while
elements outside `C/Z` are already separated by an exact representation of
a finite quotient modulo its centre.

This is an elementary argument: finite sums, residual finiteness,
simultaneous diagonalization of commuting unitaries in finite dimensions,
and extension of characters into the circle.  It uses no property (T), no
compressor, no ultrafilter, and no comparison of matrix dimensions.

DERIVATION
central-character-approximation-proof
