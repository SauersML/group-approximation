---
rg: 2
id: de-la-salle-full-pinching-rounding-proof
kind: route
title: Specialize de la Salle's two-PVM orthogonalization theorem to one reflection
target: de-la-salle-full-pinching-rounds-one-reflection
requires: []
---

Primary source: Mikael de la Salle,
[*Orthogonalization of Positive Operator Valued Measures*](https://arxiv.org/abs/2103.14126),
arXiv:2103.14126v2, Theorem 1.4; published as Theorem 4 in *Comptes
Rendus Mathématique* 360 (2022), 549--560.

The theorem starts with two PVMs `(p_i)_i,(q_j)_j` in one von Neumann
algebra and a normal state `phi`.  If

```text
sum_(i,j) ||p_i q_j-q_j p_i||_phi^2 < epsilon,
```

it constructs another PVM `(p'_i)_i` in the same algebra, commuting with
every `q_j`, with

```text
sum_i ||p_i-p'_i||_phi^2 <10 epsilon.
```

There is no dilation and no dependence on either outcome cardinality.  The
binary specialization and the tracial pinching calculation `(DFP3)` are
given in the target claim and yield `(DFP2)`.

