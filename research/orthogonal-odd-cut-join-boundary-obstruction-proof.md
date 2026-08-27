---
rg: 2
id: orthogonal-odd-cut-join-boundary-obstruction-proof
kind: route
title: Let every site preserve its own odd block and swap all the other blocks outward
target: orthogonal-odd-cut-join-amplifies-boundary-linearly
requires:
  - join-of-odd-cuts-softens-an-entire-anchor-row
---

On the four-dimensional block

```text
 K=C^2_sign tensor C^2_mem
```

put

```text
 A_0=Z tensor I,
 P=I tensor |0><0|,
 C=X tensor |0><0| + I tensor |1><1|,
 S=I tensor X.                                          (OJP1)
```

Here `C,S` are reflections.  The reflection `C` preserves `P`, anticommutes
with `A_0` on `P`, and commutes with `A_0` on `1-P`; `S` commutes with
`A_0` and swaps `P` with `1-P`.

Take `H=direct_sum_(j=1)^L K`, let `A` be the direct sum of the `A_0`, and
define `B_i` to equal `C` on block `i` and `S` on every block `j!=i`.
Then direct calculation from `(OJP1)` gives

```text
 ((B_i-AB_iA)/2)^2=P_i,                                (OJP2)
```

where `P_i` is `P` on block `i` and zero elsewhere.  Hence `p_i=P_i` at
every threshold `0<s<=1`; these projections are orthogonal and their join
`p` is `P` on every block.

Use normalized Hilbert--Schmidt norm on the `4L`-dimensional space.
On one block the unnormalized squared Frobenius norms are

```text
 ||[A_0,C]||_F^2=8,
 ||[P,S]||_F^2=4,
 ||[C,S]||_F^2=8.                                      (OJP3)
```

Therefore `[A,B_i]` is supported on block `i`, giving `2/L`.  The commutator
`[p,B_i]` is supported on the other `L-1` blocks, giving `(L-1)/L`.
For `i!=j`, `[B_i,B_j]` is `[C,S]` or its negative on exactly blocks `i`
and `j`, giving `4/L`; it vanishes for `i=j`.  Averaging proves
`(OJA2)--(OJA4)`.  Finally `P_i` has normalized trace `2/(4L)=1/(2L)`,
which proves `(OJA1)` and the impossibility statements `(OJA5)`.
