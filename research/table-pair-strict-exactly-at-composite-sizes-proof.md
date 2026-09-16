---
rg: 2
id: table-pair-strict-exactly-at-composite-sizes-proof
kind: route
title: A two-digit code at composite sizes and rectangle rigidity of the diagonal relay at prime sizes
target: table-pair-strict-exactly-at-composite-alphabet-sizes
requires: []
artifacts:
  - research/artifacts/composite-size-strict-table-2026-09-16.md
---

Complete elementary proof; notation as in the target. `T_r'` is any reverse table with `(b,1) ~ (1,1) ~ (c,a)` and
`(1,a)`, `(b,a)` not equivalent; `T_r` is one of them. Sources of `T_r'` are values `q(m,s)` constant on classes, so
`q(b,1) = q(c,a) = q(1,1) = o`, and the reverse relays read `(o, q(1,a))`, `(o, q(b,a))` and `(q(c,1), o)`.

**1. Composite sizes.**
- *Code.* Let `A = B x C` with `|B|, |C| >= 2`, projections `beta`, `gamma`, and `pi` a fixed-point-free permutation of
  `C`. Put
  - `mu(x_1, x_b, x_c) = (beta(x_c), gamma(x_1))` if `x_1 = x_b`, and `(beta(x_c), pi(gamma(x_1)))` otherwise;
  - `nu(y_1, y_a) = (beta(y_a), gamma(y_1))`.
- *`Dec(T_f)`.* Relay `1` outputs `mu(o,o,e) = (beta(e), gamma(o))`. Relay `a` outputs `mu(f,g,o)`, whose `beta`-part is
  `beta(o)`. So the sink outputs `(beta(o), gamma(o)) = o`.
- *`Enc(T_r')` fails.* The cells `(1,a)` and `(b,a)` lie in distinct classes, at most one of them the origin class, so
  the value on the other class is free. Choose `q` constant on classes with `q(1,1) = o` and
  `beta(q(1,a)) != beta(q(b,a))`. The reverse relays output `r_1 = (beta(q(1,a)), gamma(o))`,
  `r_b = (beta(q(b,a)), gamma(o))` and `r_c = (beta(o), gamma(q(c,1)))`. Since `r_1 != r_b`, the sink outputs
  `(beta(o), pi(gamma(o))) != o`.

**2. Rectangle lemma.** Let `|A| = n >= 2` and `D : A x A -> A`, and suppose `o` is a function of `(D(o,e), D(f,o))` for
all `o, e, f`. Take entropies in base `n`.
- Let `O, E, F` be independent uniform, `U = D(O,E)`, `V = D(F,O)`. Then `1 = I(O; U,V)`. `U` and `V` are
  conditionally independent given `O`, so `H(U,V | O) = H(U|O) + H(V|O)`. Together with `H(U,V) <= H(U) + H(V)`, this gives
  `I(O; U,V) <= I(O;U) + I(O;V)`.
- Let `X, Z` be independent uniform and `W = D(X,Z)`. The pair `(O,U)` has the law of `(X,W)` and `(O,V)` has the law
  of `(Z,W)`, so `I(O;U) = I(X;W)` and `I(O;V) = I(Z;W)`. Expanding each term into joint entropies gives the identity
  `I(X,Z; W) - I(X;W) - I(Z;W) = I(X;Z | W) - I(X;Z)`. Since `I(X;Z) = 0` and `I(X,Z; W) = H(W)` (as `W` is a function of
  `(X,Z)`), this reads `I(X;W) + I(Z;W) = H(W) - I(X;Z | W)`, and `H(W) <= 1`.
- So `1 <= H(W) - I(X;Z|W) <= 1`. Hence `W` is uniform, so each fiber of `D` has `n` elements. Also `I(X;Z | W) = 0`: given
  `W = σ`, the uniform distribution on the fiber has independent coordinates, so the fiber is the product of its
  projections.
- If `n` is prime, every fiber is a full row or a full column. A row and a column meet, and fibers have `n >= 2` elements,
  so all fibers are rows or all are columns. So `D(x,z) = h(x)` or `D(x,z) = k(z)`, with `h` or `k` a bijection.

**3. Prime sizes.** Let `n` be prime and let `(mu, nu)` satisfy `Dec(T_f)`. Put `D(x,z) = mu(x,x,z)`. `Dec` with `f = g`
gives `nu(D(o,e), D(f,o)) = o`, so step 2 applies.
- *Case `D = h(x)`.* For any `(y_1, y_a)`, take `o = h^{-1}(y_1)` and `f = g = h^{-1}(y_a)`; `Dec` gives
  `nu(y_1, y_a) = h^{-1}(y_1)`. The reverse relays output `r_1 = r_b = h^{-1}(o)`, so the sink outputs
  `mu(r_1, r_1, r_c) = h(r_1) = o`. `Enc(T_r')` holds.
- *Case `D = k(z)`.* `Dec` with `f = g` gives `nu(k(e), k(o)) = o` for all `e, o`, so `nu(y_1, y_a) = k^{-1}(y_a)`. Then
  `Dec` gives `k^{-1}(mu(f,g,o)) = o`, so `mu(x_1,x_b,x_c) = k(x_c)`. The sink outputs
  `k(r_c) = k(k^{-1}(q(c,a))) = o`. `Enc(T_r')` holds.

Every `n >= 2` is prime or a product of two factors at least `2`, so steps 1 and 3 prove the target. The artifact has
the full entropy computation and an independent verification. Direct evaluation covers `n = 4, 6, 8, 9`, and exhaustive
search covers `n = 2` and the lemma at `n = 2, 3`. SAT gives no strict pair at `n = 3, 5` and a strict pair at `n = 4`.
Script: `experiments/composite-size-strict-table-2026-09-16/verify_composite_table.py`.
