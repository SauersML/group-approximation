---
rg: 2
id: atlas-19243-centrality-is-bar-s-consequence-proof
kind: route
title: Kernel membership makes every fixed commutator a packet consequence
target: atlas-19243-centrality-is-bar-s-consequence
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - atlas-word-19243-is-kernel-relation
---

By `atlas-word-19243-is-kernel-relation`,

```text
q_19243 in N=ker(bar_rho).
```

Since `x=p1_12` lies in `bar_P`, the defining subgroup commutator relation gives

```text
[x,q_19243] in [bar_P,N]=bar_N.
```

The canonical atlas criterion states that `bar_S` is a finite normal
generating set for this very subgroup `bar_N`.  Hence for this fixed word there
is a finite expression

```text
c_19243 = product_(j=1)^L g_j s_j^(eps_j) g_j^(-1),

s_j in bar_S,  eps_j in {+1,-1}.
```

For any unitary representation, bi-invariance of normalized Hilbert--Schmidt
distance gives the same defect for a conjugate, inversion preserves distance
to the identity, and telescoping products gives

```text
||pi(c_19243)-1||_2
 <= sum_j ||pi(s_j)-1||_2
 <= L max_(s in bar_S)||pi(s)-1||_2.
```

Take `L_19243=L`.  Therefore the centrality defect is `o(1)` in every sequence
whose canonical packet defect is `o(1)`.