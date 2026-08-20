---
rg: 2
id: boolean-predicate-is-one-rank-jump-proof
kind: route
title: Disjoint-path branching program, unitriangular inverse, Schur complement
target: boolean-predicate-is-one-rank-jump
requires: []
---

Write the indicator of an assignment `a` as `delta_a(x) = prod_i l_(a_i)(x_i)`
with `l_1(x_i) = x_i` and `l_0(x_i) = 1 + x_i`, arithmetic in `F_2`.  On the
Boolean cube `delta_a(x) = 1` exactly when `x = a`, so

```text
f(x) = sum_(a : f(a)=1) delta_a(x).
```

Build a directed acyclic graph with a source `s`, a sink `t`, and one
internally vertex-disjoint `s`-to-`t` path per satisfying assignment `a`, the
`i`-th edge of that path labelled `l_(a_i)(x_i)`.  Vertex-disjointness of the
interiors means the only `s`-to-`t` paths are the designated ones, so the
path-sum is exactly the display above.

Order the vertices topologically and let `N_f(x)` be the weighted adjacency
matrix, which is strictly upper triangular, and put `U_f(x) = I + N_f(x)`.
`U_f(x)` is unitriangular, hence invertible over `F_2` for every `x`, which is
the second assertion.  Since `N_f` is nilpotent,

```text
U_f(x)^(-1) = I + N_f(x) + N_f(x)^2 + ...
```

(over `F_2` there is no sign to track), and `(N_f^m)_(s,t)` is the sum of the
weights of the directed `s`-to-`t` paths of length `m`.  Summing over `m`,

```text
e_s^T U_f(x)^(-1) e_t = f(x).
```

Now set

```text
M_f(x) = [[U_f(x), e_t],
          [e_s^T,   0 ]].
```

Because the leading block is invertible, the Schur-complement rank formula
applies:

```text
rank M_f(x) = rank U_f(x) + rank(0 - e_s^T U_f(x)^(-1) e_t)
            = N + rank(f(x))
            = N + f(x),
```

the last step because a one-by-one matrix has rank equal to its entry when the
entry lies in `{0,1}`.  This is `(BPR1)`.

For `(BPR2)`, take `k=2` and the single satisfying assignment `(1,1)`: the
branching program is `s -> v -> t` with labels `x` and `y`, and the displayed
two-by-two matrix is the resulting `M_f` after deleting the vertex `v`, whose
row and column are trivial.  Direct check: the matrix has rank one unless
`x = y = 1`, where it has rank two.

Every step is finite `F_2` linear algebra and the construction is effective
from the truth table.
