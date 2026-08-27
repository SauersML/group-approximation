---
rg: 2
id: joint-pinching-costs-linear-generator-gap
kind: claim
title: Joint-PVM pinching has a sharp linear gap from averaged generator commutators
distinct_from:
  sparse-clifford-cycles-refute-average-commutator-rounding: that gives a global far tuple with sparse signed commutation; this is an exact Fourier identity for one operator relative to an already commuting reflection tuple.
  complete-overlay-row-newton-is-a-code-riesz-multiplier: that identifies the inverse of the full balanced linearized overlay; this isolates the elementary abelian generator Laplacian before parity/code constraints are used.
  de-la-salle-full-pinching-rounds-one-reflection: that rounds from full joint-pinching disturbance; this proves that balanced average pair energy alone does not bound that input uniformly.
---

ESTABLISHED.  Let `S_1,...,S_k` be commuting reflections in a finite tracial
von Neumann algebra, let `Q` be their joint spectral PVM, and put

```text
D_S(R)=(1/k)sum_i ||[R,S_i]||_2^2                         (JPG1)
```

for any `R in L_2(M)`.  Then

```text
(1/4)D_S(R) <= ||R-E_Q(R)||_2^2 <= (k/4)D_S(R).           (JPG2)
```

Both constants are sharp.

For the proof, the commuting involutions `Ad(S_i)` give the orthogonal
Fourier decomposition

```text
R=sum_(a in F_2^k) R_a,
Ad(S_i)(R_a)=(-1)^(a_i)R_a.                              (JPG3)
```

The joint pinching is the group average, so

```text
||R-E_Q(R)||_2^2=sum_(a!=0)||R_a||_2^2,
D_S(R)=(4/k)sum_a |a| ||R_a||_2^2.                       (JPG4)
```

Since `1<=|a|<=k` off the zero character, `(JPG2)` follows.  Support on a
weight-one character attains the upper bound in `(JPG2)`; support on the
all-one character attains the lower bound.

Consequently de la Salle's cardinality-free two-PVM theorem cannot be fed
from the balanced complete-pair term alone.  If its previously rounded PVM
has `k` binary coordinates, the overlay controls the left side of `(JPG1)`
on average, whereas its hypothesis is the middle term of `(JPG2)`.  A
weight-one adjoint mode incurs the unavoidable factor `k` even though the
target PVM has already been exactified.

Parity is precisely the possible escape: a parity/code estimate could force
the nonzero adjoint Fourier mass in `(JPG3)` onto characters of weight
`Omega(k)`, making the two quantities comparable.  For an approximate
occurrence tuple, however, those joint characters do not exist before
synchronization.  Thus an applicable theorem must first manufacture an
approximate spectral decomposition while using the balanced parity energy,
or prove the equivalent square-function coercivity directly.  This is the
noncentral content of `balanced-overlay-diffuse-square-function-newton`;
generic PVM orthogonalization and fixed-graph HS stability stop after that
gate rather than proving it.

