---
rg: 2
id: tensor-independent-child-carrier-gap
kind: claim
title: Tensor-independent child algebras cannot both recover one fixed-density carrier
---

Let `(M,tau)` be a finite tracial von Neumann algebra and let `A,B subset M`
be unital von Neumann subalgebras which are trace-independent in the strong
sense

```text
tau(a b)=tau(a)tau(b)   for all a in A, b in B.
```

For every projection `F in M` of trace `c=tau(F)`, one has

```text
dist_2(F,A)^2 + dist_2(F,B)^2 >= c(1-c).
```

In particular

```text
max(dist_2(F,A)^2,dist_2(F,B)^2) >= c(1-c)/2.
```

For the Pauli/Leavitt transported carrier of trace `c=1/4`, the lower bound is
`3/32` on at least one side.

The rectangular escape model has exactly this geometry: after identifying the
two independent child coordinate packets with tensor factors, their generated
matrix algebras are `M_N tensor 1` and `1 tensor M_N`, which are
trace-independent.  Hence rectangular escape is impossible as soon as the
mixed relations recover **one and the same** fixed-density nontrivial carrier
inside `o(1)` of both child algebras.  This does not by itself prove
`same-orbit-closure`; it isolates a dimension-free certificate that would kill
the known countermodel without any cardinality or orbit-counting argument.
