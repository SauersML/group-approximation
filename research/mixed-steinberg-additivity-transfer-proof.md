---
rg: 2
id: mixed-steinberg-additivity-transfer-proof
kind: route
title: Expand one commutator of a product and reorder five active coordinates
target: mixed-steinberg-triangles-transfer-actor-additivity
requires: []
---

Use the commutator convention `[x,c]=xcx^(-1)c^(-1)`.  The exact identity

```text
[xy,c]=x[y,c]x^(-1)[x,c]                               (MSP1)
```

with `x=X(b)` and `y=X(a)` gives

```text
[X(b)X(a),C]
 =X(b)[X(a),C]X(b)^(-1)[X(b),C].                      (MSP2)
```

Under `(MST2)`, the right side is

```text
X(b)Y(a)X(b)^(-1)Y(b)=Y(a)Y(b),                       (MSP3)
```

which proves `(MST3)`.

For the quantitative statement, normalized Hilbert--Schmidt distance is
bi-invariant.  Replacing the first argument of a commutator changes the
commutator by at most twice that distance.  Starting from `Y(a+b)`, make the
following replacements:

1. replace it by `[X(a+b),C]`, cost at most `epsilon`;
2. replace `X(a+b)` by `X(b)X(a)`, cost at most `2 epsilon`;
3. use `(MSP1)` exactly;
4. replace the two commutators by `Y(a)` and `Y(b)`, total cost at most
   `2 epsilon`;
5. remove conjugation of `Y(a)` by `X(b)`, cost at most `epsilon`.

The total is `6 epsilon`, proving `(MST5)`.

For `(MST7)`, expand `phi(a)phi(b)`.  Move each `Y_i(b_i)` left until it is
adjacent to `Y_i(a_i)`.  There are

```text
4+3+2+1=10                                             (MSP4)
```

cross-coordinate swaps, costing at most `10 eta`.  Apply `(MST5)` in the
five coordinates, costing at most `5*6 epsilon`.  This proves `(MST7)`.

The proof also identifies why adding the full mixed triangles kills the
partial graph-product model.  In that model `X(b)` acts by the true linear
transvection, so `(MSP2)` says that its commutator with the seed must equal
the graph-product difference between two addressed vertices.  Requiring
this difference to be the named `Y(b)` for every `b`, together with the
additive actor-root row, imposes `(MST3)` for every remote ratio.  There is no
zero-defect nonlinear escape satisfying all these premises; the escape can
only move one level upward into failure of the actor-root additive table.

