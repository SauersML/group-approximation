---
rg: 2
id: lin-code-space-low-rank-perfect-strategy-proof
kind: route
title: Factor the restricted dot product and label its spectral characters
target: lin-code-space-pauli-test-has-only-logarithmic-weyl-rank
requires: []
---

The source text was checked directly in `Introspection.tex` from the v1
arXiv source.  It says that `S_n^PB` is the code space of a Justesen code of
length `n` and dimension `floor(log n)`, and that the sampler is a bijection
from all `floor(log n)`-bit messages onto this space.  Thus `S_n^PB` is
literally a proper linear subspace of `F_2^n`, not a spanning list of
generator-matrix columns.

For a general `k`-dimensional `C`, choose a full-column-rank matrix `G` with
image `C`.  Rank factorization over `F_2` gives

```text
G^T G=L R,
L:F_2^r -> F_2^k,       R:F_2^k -> F_2^r,
```

with both factors of rank `r`.  On the standard `r`-qubit Pauli system,
define `(LCW2)`.  The standard commutator formula gives

```text
X(L^T a)Z(Rb)=(-1)^((L^T a).(Rb))Z(Rb)X(L^T a)
             =(-1)^(a^T G^T G b)Z_C(Gb)X_C(Ga).
```

The maps are additive, so every same-basis parity relation is exact.

It remains to realize the fine `(Pauli,W)` answer alphabet.  The transpose
`G^T:F_2^n -> F_2^k` is onto.  Each simultaneous eigenspace of the commuting
`X_C(C)` family has a character `lambda in C^*`; choose
`s(lambda) in F_2^n` satisfying

```text
(Ga).s(lambda)=lambda(Ga)          for every a.
```

Assign that eigenspace to fine answer `s(lambda)` and assign zero to every
unused answer.  Then the parity of the fine answer against any `u in C` is
the spectral PVM of `X_C(u)`.  The same construction works for `Z_C`.
Figure 6 only compares a fine answer through these parities, self-
consistency, commuting joint measurements, or a magic-square context.
Equation `(LCW3)` supplies the first three, and the standard one-ancilla
magic-square completion supplies the last.  The EPR transpose construction
makes the strategy synchronous and oracularizable.

For the dense kernel element, take `v` uniformly in `C^perp`.  The coordinate
functional `v -> v_i` is identically zero only if `e_i` lies in
`(C^perp)^perp=C`.  A `k`-dimensional space contains at most `k` distinct
standard basis vectors.  Hence

```text
E |v| >= (n-k)/2,
```

and some `v` has at least that weight.  For this `v`, `u.v=0` for every
queried `u`, so `Z(v)` and every function of it commute with all queried
`X(u)`.  This proves the exact coherent-kernel assertion.

Finally, a nonzero character of `F_2^n/C` is an eigenvector with eigenvalue
one for convolution by uniform measure on `C`, but is not invariant under
`F_2^n`.  Therefore the measure has no spectral gap relative to the full
group.  De la Salle's source states the correct converse construction:
for a code of length `K` and dimension `n`, a basis identifies the `K`
coordinate functionals with a spanning subset of `F_2^n`.  This proves both
the failure of the literal citation and the generator-column repair.

