---
rg: 2
id: kazhdan-haagerup-atomic-image-proof
kind: route
title: Rigidity makes a compact deformation uniform on the image, so its unit ball is totally bounded
target: kazhdan-images-in-haagerup-algebras-are-atomic
requires: []
---

Notation as in the target: `Lambda` has property (T) with Kazhdan pair
`(S,kappa)`, `B = sigma(Lambda)''` is a finite von Neumann algebra with the
Haagerup property, and `tau` is its faithful normal trace.

**Step 1 (deformation).** By the Haagerup property there are normal
completely positive maps `phi_k : B -> B` with `phi_k(1) <= 1`,
`tau o phi_k <= tau`, `||phi_k(x) - x||_2 -> 0` for every `x in B`, and each
`phi_k` extends to a compact operator `T_k` on `L^2(B)`.

**Step 2 (pointed correspondence).** For `phi = phi_k` let `H_phi` be the
completion of `B tensor_alg B` for `<a tensor b, c tensor d> = tau(b^* phi(a^* c) d)`
(positive because `phi` is completely positive), with bimodule actions
`x (a tensor b) y = xa tensor by` and vector `xi = 1 tensor 1`. Then

```text
<x xi y, xi> = tau(phi(x) y),          ||x xi||^2 = tau(phi(x^* x)).
```

For a unitary `u in B`,

```text
||u xi - xi u||^2 = tau(phi(1)) + tau(u^* phi(1) u) - 2 Re tau(phi(u^*) u)
                 <= 2 - 2 Re tau(phi(u) u^*) <= 2 ||u - phi(u)||_2 .
```

**Step 3 (rigidity).** `pi(gamma) eta = sigma(gamma) eta sigma(gamma)^*` is a
unitary representation of `Lambda` on `H_phi`, and
`||pi(s) xi - xi|| = ||sigma(s) xi - xi sigma(s)||`. Choose `k` with
`max_(s in S) ||sigma(s) - phi_k(sigma(s))||_2 <= delta`. By property (T) the
projection `eta` of `xi` onto the `pi`-invariant vectors satisfies
`||xi - eta|| <= kappa^(-1) sqrt(2 delta)`. An invariant vector commutes with
`sigma(Lambda)`, hence, by normality of both actions, with every `x in B`.
For `||x|| <= 1` the two actions are contractions, so

```text
||x xi - xi x|| <= ||x (xi - eta)|| + ||(eta - xi) x|| <= 2 kappa^(-1) sqrt(2 delta) =: eps.
```

Expanding as in Step 2, using `phi(x)^* phi(x) <= phi(x^* x)` (Kadison--Schwarz
for a subunital completely positive map) and `Re tau(x^* phi(x)) = Re tau(phi(x^*) x)`,

```text
||phi(x) - x||_2^2 <= ||x xi - xi x||^2 + tau(x^* (1 - phi(1)) x)
                  <= eps^2 + ||1 - phi_k(1)||_2 .
```

Letting `delta -> 0` along the deformation gives
`sup_(||x|| <= 1, x in B) ||phi_k(x) - x||_2 -> 0` on a subsequence.

**Step 4 (compactness).** The unit ball of `B` lies within `o(1)` of
`phi_k(ball B)`, which lies in the precompact set `T_k(ball L^2(B))`. So the unit
ball of `B` is totally bounded in `||.||_2`.

**Step 5 (atomicity).** Write `B = B_at + B_d`, with `B_at` the sum of the
minimal central summands that are finite-dimensional factors. If `B_d != 0` it
has no normal finite-dimensional representation, so it contains a diffuse
abelian subalgebra and hence a unitary `u` in the corner with
`tau(u^n) = 0` for `n != 0`. Then `||u^n - u^m||_2^2 = 2 tau(1_(B_d))` for
`n != m`, contradicting total boundedness. So `B = B_at`, every summand is a
finite factor with minimal projections, i.e. `M_(n_k)(C)`, and `L^2(M)` splits
under `sigma(Lambda)` as `directSum_k C^(n_k) tensor K_k`. This is `(KHA1)`.
