---
rg: 2
id: stw99-xciv-two-norm-centrality-obstruction-proof
kind: route
title: Put anticommuting Pauli pairs on vanishing-trace orthogonal corners
target: stw99-xciv-two-norm-centrality-does-not-control-norm-centrality
requires: []
---

Choose pairwise orthogonal nonzero projections `q_n in R` with
`tau(q_n) -> 0`.  Each corner `q_n R q_n` is a II1 factor, so it contains
selfadjoint unitaries (with corner unit `q_n`) `a_n,b_n` satisfying

```text
a_n b_n = -b_n a_n,       tau(b_n)=0.
```

For example, take the two Pauli generators in a unital `M_2` inside the
corner.  The orthogonal strong sum

```text
x = strong-sum_n a_n
```

belongs to `R` and is a selfadjoint contraction.  Define

```text
u_n = 1-q_n+b_n.
```

This is a selfadjoint unitary.  Since `b_n^2=q_n` and `tau(b_n)=0`,

```text
||u_n-1||_2^2 = ||b_n-q_n||_2^2 = 2 tau(q_n) -> 0.
```

For every fixed `y in R`, the tracial ideal estimate gives

```text
||[u_n,y]||_2
 <= ||(u_n-1)y||_2 + ||y(u_n-1)||_2
 <= 2 ||y|| ||u_n-1||_2 -> 0.
```

On the other hand, `u_n` commutes with every `a_m` for `m != n`, because
their support projections are orthogonal, while on `q_n` one has

```text
[u_n,a_n]=[b_n,a_n]=2b_n a_n
```

up to sign.  The last operator has norm `2`.  Therefore
`||[u_n,x]||=2` for every `n`, as asserted.

Equivalently, the canonical quotient from the norm sequence algebra to the
tracial sequence algebra has a large kernel: the norm-one sequence `(q_n)`
survives modulo `c_0(R)` but vanishes modulo the trace-kernel ideal.  The
construction above shows that this loss is not merely radial; it can erase a
maximal commutator with one fixed element of `R`.
