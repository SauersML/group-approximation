---
rg: 2
id: stw81-stabilization-unitization-reduction-proof
kind: route
title: Preserve the shadow invariant and nuclear dimension under the two standard enlargements
target: stw81-counterexamples-reduce-to-stable-and-unital
requires:
  - stw81-ctdim-extension-maximum
  - stw81-ctdim-morita-invariance
artifacts:
  - research/artifacts/stw81-type-i-frontier-2026-08-30.md
---

Let `A` satisfy the LXXXI shadow hypothesis and have

```text
2 <= dim_nuc(A) < infinity.
```

Strong Morita invariance gives

```text
ctdim(A tensor K)=ctdim(A)<=1.
```

Nuclear dimension is invariant under stabilization, so
`dim_nuc(A tensor K)=dim_nuc(A)`.  Hence `A tensor K` is a stable
counterexample.

For the minimal unitization use the extension

```text
0 -> A -> A~ -> C -> 0.
```

The `ctdim` maximum formula and `ctdim(C)=0` give

```text
ctdim(A~)=ctdim(A)<=1.
```

Nuclear dimension agrees with that of the minimal unitization, including
the zero-dimensional case, so `dim_nuc(A~)=dim_nuc(A)`.  Thus `A~` is a
unital counterexample.

Finally, `stw81-continuous-trace-shadow-invariant` converts each `ctdim<=1`
statement back into the original hereditary-shadow hypothesis.

**Trust boundary.**  The only additional standard input is invariance of
nuclear dimension under stabilization and minimal unitization.
