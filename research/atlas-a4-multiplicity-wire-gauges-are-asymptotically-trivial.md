---
rg: 2
id: atlas-a4-multiplicity-wire-gauges-are-asymptotically-trivial
kind: claim
title: The normalized exact A4 network has asymptotically identity local multiplicity-wire gauges
---

In the normalized exact A4 context network, choose for every context `c` the
near-identity exact Schur gauge `Z_(c,n)` of
`atlas-a4-context-near-identity-schur-gauges`.

Fix one canonical coherence branch, say `j=0`, and write

```text
T_(c,n): R_(c,0) H_n -> S_c H_n,
T_(chart,c,n): R_(chart,c,0) H_n -> S_(chart,c) H_n
```

for the corresponding partial unitaries of the context and its literal chart
A4 pair.  Then the induced multiplicity-wire transport

```text
V_(c,n) = T_(chart,c,n) Z_(c,n) T_(c,n)^*
```

satisfies, as an ambient partial isometry,

```text
||V_(c,n)-S_c||_2 -> 0,                               (A4-WIRE-ID)
```

uniformly over the thirty contexts; equivalently it is `o(1)` from the natural
identity transport between the two asymptotically equal carrier subspaces.
The same conclusion holds for `j=1,2`, and the three formulas agree because
`Z_(c,n)` is an exact A4 intertwiner.

Therefore a hypothetical counterexample to the A4 holonomy gap cannot exploit
an `O(1)` unitary rotation on external multiplicity at any individual context.
Any surviving obstruction must be a genuinely global finite-chart holonomy,
not local high-dimensional mixing.