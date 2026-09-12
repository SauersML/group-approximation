---
rg: 2
id: sparse-clifford-cycles-refute-average-commutator-rounding
kind: claim
title: Sparse Clifford cycles refute generic average-commutator rounding
distinct_from:
  positive-rate-tanner-tests-have-contextual-models: that uses local code solution groups and an exterior-square dimension count; this is an explicit tuple with vanishing complete-pair commutator energy and a constant rounding obstruction.
  bounded-degree-clouds-have-logarithmic-root-gauge-leak: that varies gauges across equality copies; this has one globally named reflection per coordinate and no equality layer.
---

For arbitrarily large `L` there are finite-dimensional reflections
`A_1,...,A_L` whose commutation signs form a cycle:

```text
A_i A_j=(-1)^(1_{{i,j} is a cycle edge}) A_j A_i.          (SCC1)
```

Their complete ordered-pair commutator energy is

```text
(1/L^2)sum_(i,j)||A_iA_j-A_jA_i||_2^2=8/L ->0.             (SCC2)
```

Nevertheless every commuting reflection tuple `B_1,...,B_L` satisfies

```text
(1/L)sum_i ||A_i-B_i||_2^2 >=1/4.                          (SCC3)
```

Thus no dimension-independent theorem can round an arbitrary reflection
tuple from small **average** pairwise commutator energy alone.  In the
repeated-LDPC route the parity/codeword PVM constraints are load-bearing;
the complete commutation overlay cannot be passed directly to generic
abelian HS stability.
