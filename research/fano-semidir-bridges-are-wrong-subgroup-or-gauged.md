---
rg: 2
id: fano-semidir-bridges-are-wrong-subgroup-or-gauged
kind: claim
title: Finite Fano bridges either preserve the wrong subgroup or carry an actor gauge
invalidates:
  - finite-fano-semidir-supplies-moving-square-bridges
artifacts:
  - research/fano-semidir-bridge-dichotomy-proof.md
distinct_from:
  fano-moving-packet-retains-actor-holonomy: that tensors the whole actor table and exhibits the surviving order-seven holonomy; this proves no element of the finite semidirect packet can be the ungauged parallel bridge needed to remove it.
  middle-index-order-seven-orbit-cut-is-native-scale-neutral: that studies the invariant zero-character atom; this uses the actual signed Hecke subgroup and its nontrivial Singer translate.
  el20-six-moving-coefficient-square-bridges: that permits words using the full Leavitt coefficient presentation outside the finite Fano semidirect packet; this refutes only the internal finite-packet search.
---

**ESTABLISHED FINITE-SEMIDIRECT BRIDGE DICHOTOMY.**  Let `A` be the
seven-pair extraspecial packet and `K` its finite binary actor group.  The
current finite closure is the semidirect packet `A semidirect K`.  Let
`L_0<=K` be the actor subgroup defining the signed common Hecke source `Q`,
and let `t=t_1` be the first Singer head.

The subgroup moves genuinely under `t`.  In the seven-coordinate actor
basis `(2,4,5,6,7,8,9)`, `L_0` contains

```text
d=I+e_2e_8^*.                                         (FSD1)
```

The Singer matrix on `(4,7,8)` sends the source covector `e_8^*` to
`e_7^*`, hence

```text
t d t^(-1)=I+e_2e_7^*.                                (FSD2)
```

Every displayed generator of `L_0` fixes the vector `e_7`: in the directed
transvection list

```text
6->5, 5->4, 4->2, 8->2, 9->4, 9->2,
9->7, 5->7, 6->7, 6->8,                              (FSD3)
```

the coordinate `7` is never a source.  Therefore every element of `L_0`
fixes `e_7`, while `(FSD2)` does not, and

```text
tL_0t^(-1)!=L_0.                                      (FSD4)
```

Now take any word `w in A semidirect K` intended to carry `Q` to `tQt^*`.
If its actor quotient is the identity, conjugation by `w` preserves the
`K`-Fourier support `L_0`: a Pauli factor can change phases but not the
actor quotient of any term.  By `(FSD4)` it cannot produce the target
support `tL_0t^(-1)`.

If the actor quotient `k` of `w` is nontrivial, use the exact packet model

```text
a |->rho_0(a) tensor 1,
k'|->U(k') tensor lambda_K(k').                       (FSD5)
```

The bridge then carries the nontrivial reservoir unitary `lambda_K(k)`.
All finite packet multiplication and covariance relations remain exact, so
no estimate using only that table can replace this factor by the identity.

Thus the internal finite Fano packet has an exact dichotomy: its ungauged
words preserve the wrong actor subgroup, and its subgroup-moving words are
reservoir-gauged.  A successful bridge must use a coefficient-sensitive
full-EL20 relation outside this finite semidirect table, together with a
matrix-only full-Gram estimate.

DERIVATION
fano-semidir-bridge-dichotomy-proof
