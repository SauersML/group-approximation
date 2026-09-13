---
rg: 2
id: howie-pro-p-tuple-fails-at-a5-proof
kind: route
title: Abelianize to see perfection, read off the central extension of the (2,3,5) triangle group, and evaluate at explicit permutations
target: howie-pro-p-tuple-fails-the-profinite-certificate-at-a5
requires: []
---

**1. `P` is perfect.** Exponent sums in `(x, y)`: `g_1` gives `(-2, -3)` and
`g_2 = x^-2 (xy)^5` gives `(3, 5)`. The determinant is `(-2)(5) - (-3)(3) = -1`,
so the relators span `Z^2` and `P^ab = 0`.

**2. A central element.** In `P`, `z := x^2 = y^-3 = (xy)^5`. It is a power of `x`,
so it commutes with `x`. It is a power of `y`, so it commutes with `y`. So `z` is
central.

**3. The quotient.** `P/<z> = <x, y | x^2, y^3, (xy)^5>` is the von Dyck group
`D(2,3,5)`, isomorphic to `A_5`, of order 60.

**4. The central kernel is small.** For a central extension `1 -> C -> P -> Q -> 1`,
the five-term exact sequence reads

```text
H_2(P) -> H_2(Q) -> C / [P, C] -> H_1(P) -> H_1(Q) -> 0 .
```

Here `[P, C] = 1` and `H_1(P) = 0`, so `H_2(A_5) = Z/2` surjects onto `C = <z>`.
Hence `|z| <= 2` and `|P| <= 120`.

**5. Explicit evaluation.** Compose permutations right to left. Take
`X = (1 2)(3 4)` and `Y = (1 3 5)` in `A_5`.
- `X^2 = 1` and `Y^3 = 1`.
- `XY` sends `1 -> 4 -> 3 -> 5 -> 2 -> 1`, so `XY = (1 4 3 5 2)` and `(XY)^5 = 1`.
- So `g_1(X, Y) = X^-2 Y^-3 = 1` and `g_2(X, Y) = X^-2 (XY)^5 = 1`.
- `a(X, Y) = X Y^2 = X Y^-1`, with `Y^-1 = (1 5 3)`. Then `X Y^-1` sends `1` to
  `X(5) = 5`, so it is nontrivial.

(Left-to-right composition replaces `XY` by `YX`, which is conjugate to it, and
changes nothing.)

**6. The certificate fails.** Let `q : F -> A_5` send `x -> X` and `y -> Y`. Then
`[q(g_1)] [q(g_2)] = {1}` and `q(a) != 1`. So `q(a)` is not in the product of the
two conjugacy classes, and condition (2) of the certificate fails.

**7. The general necessary condition.** Let `(g_1, ..., g_k; x)` satisfy condition (2),
and let `q : F -> Q` be a finite quotient that kills every `g_i`. Condition (2) gives
`q(x) in {1}`. So `x` is killed by every finite quotient of `F/N(g_1, ..., g_k)`.
Since `x` is not in `N(g_1, ..., g_k)` by condition (1), the presented group is not
residually finite.

**On the pro-`p` statement.** The pro-`p` claim is consistent with all of this.
`P` is perfect, so every nilpotent quotient of `P` is trivial. So `a` dies in every
nilpotent quotient of `F` that kills the `g_i`. Howie's one-conjugate-each identity
modulo the derived series is a sharper statement, and Step 6 does not contradict it.
