---
rg: 2
id: finite-depth-contractive-computation-ladder
kind: claim
title: A fixed marked floor needs only a constant number of contraction cells
distinct_from:
  contractive-computation-ladder: that sends the recursion depth to infinity and therefore assumes one coherent infinite ladder; this keeps the terminal term and chooses one finite depth depending only on the fixed marked floor.
---

Let `0<lambda<1`, let `p` be a fixed nonnegative polynomial, and let
`a_0,...,a_m` be nonnegative numbers with `a_m<=A`.  Suppose that

```text
a_n <= lambda a_(n+1)+C p(n) sqrt(E)       (0<=n<m),             (FDL1)
```

and that the marked interface gives

```text
a_0 >= a_*-K_0 sqrt(E),                    a_*>0.                 (FDL2)
```

Put

```text
S_m=sum_(n=0)^(m-1) lambda^n p(n).
```

Then

```text
a_0 <= lambda^m A+C S_m sqrt(E).                                  (FDL3)
```

Consequently, if the **constant** depth `m` is chosen so that
`lambda^m A<=a_*/2`, then

```text
E >= a_*^2 / (4(K_0+C S_m)^2)>0.                                  (FDL4)
```

Thus an obstruction with a fixed positive marked floor does not require an
infinite tape, a shift repeating one cell at every level, or exactification
uniform in an unbounded accumulated packet rank.  It requires only the first
`m` contraction cells, where `m` depends on the fixed construction constants
and not on the matrix dimension or target microstate accuracy.

This is only the scalar endpoint.  It does not construct the finite nested
Schur packet chain or its matrix-only comparison maps.
