---
rg: 2
id: simple-torsion-mf-character-proof
kind: route
title: Take trace limits after macroscopic torsion reblocking
target: simple-torsion-non-mf-iff-trivial-mf-characters
requires:
  - simple-torsion-groups-have-a-macroscopic-mf-dichotomy
---

If `Rad_MF(G)=G`, the corona homomorphism defined by any operator-norm
asymptotic representation is trivial.  Hence, for every fixed `g`,
`||sigma_n(g)-I|| -> 0`, so its normalized trace tends to one.

Conversely suppose the MF radical is not all of `G`.  Simplicity makes it
trivial, and the macroscopic dichotomy supplies an operator-norm
asymptotic representation with

```text
liminf_n ||sigma_n(g)-I||_2>0                         (1)
```

for every `g!=1`.  Since `G` is countable, pass diagonally to a subsequence
on which all normalized traces converge.  Operator-norm multiplicativity
makes the limit conjugation invariant.  Positive definiteness follows by
replacing `tr(sigma_n(g_i^(-1)g_j))` with
`tr(sigma_n(g_i)^*sigma_n(g_j))`; the difference tends to zero on every
fixed finite tuple.

For a unitary `U`,

```text
||U-I||_2^2=2-2 Re tr(U).                              (2)
```

Equations `(1)--(2)` imply `Re chi(g)<1` for every nonidentity `g`.
Thus `chi` is a nontrivial MF character, proving the reverse implication.
