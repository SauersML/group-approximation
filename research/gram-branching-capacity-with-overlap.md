---
rg: 2
id: gram-branching-capacity-with-overlap
kind: claim
title: Branch capacity survives nonorthogonal ranges with a Gram-overlap penalty
---

Let `(M,tau)` be a finite tracial von Neumann algebra, let `P` be a projection,
and let `T_1,...,T_N` be partial isometries with source projections
`E_a=T_a^*T_a`.  Put

```text
s = sum_a tau(E_a),
l = sum_a ||(1-P)T_a||_2^2,
o = sum_(a != b) ||T_a^* T_b||_2^2,
x = tau(P).
```

Then

```text
(s-l)^2 <= x (s+o),                                  (GBC1)
```

and therefore

```text
x >= s - 2l - o.                                     (GBC2)
```

Consequently the Perron--Frobenius branching-collapse theorem remains valid
when incoming branch ranges are only approximately orthogonal: at target `j`,
replace the exact leakage error `e_j` by

```text
2 l_j + o_j,
```

where `l_j` is total off-target branch leakage and `o_j` is the ordered-pair
Gram overlap energy of the incoming branches.

This is dimension-free and uses normalized Hilbert--Schmidt energy.  It is the
right robustness interface for a finite branch automaton extracted from atlas
microstates: exact orthogonality is unnecessary as long as wrong-target mass
and cross-branch Gram energy both vanish.