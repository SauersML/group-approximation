---
rg: 2
id: atlas-a4-context-near-identity-schur-gauges-proof
kind: route
title: Stable letters make the identity a near intertwiner, then Schur-average it
target: atlas-a4-context-near-identity-schur-gauges
requires:
  - atlas-a4-context-exact-regular-normalization
  - a4-regular-quantitative-schur-gauge
---

Fix one context `c`.  In the graph-of-groups presentation, each cyclic edge
identification is either a tree identification or has a stable letter.  Write
`t_a,t_b` for the corresponding exactifying unitaries, taking `t=I` on a tree
edge.  The exact graph-of-groups relations give, after choosing orientations,

```text
t_a sigma_n(a_c) t_a^* = sigma_n(A_c),
t_b sigma_n(b_c) t_b^* = sigma_n(B_c).
```

By `atlas-a4-context-exact-regular-normalization`, every non-tree stable letter
is `o(1)` from `I`; hence

```text
||sigma_n(a_c)-sigma_n(A_c)||_2 <= 2||t_a-I||_2=o(1),
||sigma_n(b_c)-sigma_n(B_c)||_2 <= 2||t_b-I||_2=o(1).   (1)
```

The A4 context representation is exactly `1680 k_n Reg(A4)`.  The restriction
of the adjacent chart representation `k_n Reg(A8)` to the literal subgroup
`<A_c,B_c> ~= A4` is also exactly

```text
[A8:A4] k_n Reg(A4) = 1680 k_n Reg(A4).
```

Thus the two exact A4 representations in `(1)` have identical regular type.
Apply `a4-regular-quantitative-schur-gauge` with the ambient identity unitary
`U=I`.  Its generator defect is `o(1)`, so it returns an exact A4 intertwiner
`Z_(c,n)` satisfying

```text
||Z_(c,n)-I||_2=o(1).
```

The number of contexts is the fixed number thirty, so the convergence is
uniform after taking the maximum over `c`.

Finally the quantitative Schur-gauge theorem, together with the canonical
factorization `a4-coherence-fan-canonically-splits-multiplicity` used in its
proof, says that the restriction of every exact `Z_(c,n)` to the
three-dimensional coherence sector is exactly

```text
I_3 tensor V_(c,n).
```

Therefore the local qutrit register is fixed and all residual overlap freedom
is confined to the multiplicity factor, proving the claim.