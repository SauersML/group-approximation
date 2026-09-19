---
rg: 2
id: universal-fixed-projection-forces-kazhdan-subgroup-proof
kind: route
title: Approximate the coset state of delta_eN by induced vector states on the coset N, where N has no fixed vectors, and evaluate the substitute on both sides
target: universal-fixed-projection-forces-kazhdan-subgroup
requires: []
---

Notation is that of the target. Representations of `Gamma` are identified with
representations of `C*(Gamma)`.

## Step 0: the fixed projection commutes with the commutant

Let `rho` be a unitary representation of `Gamma` and let `T in rho(N)'`.
- If `rho(n) xi = xi` for all `n in N`, then `rho(n) T xi = T rho(n) xi = T xi`.
  So `T` maps `Fix rho(N)` into itself.
- The same holds for `T^* in rho(N)'`. So `Fix rho(N)` reduces `T`, and
  `T F_rho = F_rho T`.

## Step 1: induced representations and the coset N

Let `sigma` be a unitary representation of `N` on `H`.

**The model of `Ind sigma`.**
- The space `H_rho` consists of the functions `f: Gamma -> H` with
  `f(g n) = sigma(n)^(-1) f(g)` for `n in N`, and with
  `sum over gN in Gamma/N of ||f(g)||^2 < infinity`. The summand is constant on cosets.
- The action is `(rho(gamma) f)(g) = f(gamma^(-1) g)`.
- For a coset `c = gN`, let `H_c` be the functions supported on `c`. Then
  `H_rho` is the orthogonal sum of the `H_c`, and `rho(gamma) H_c = H_(gamma c)`.

**The coset N.**
- `N` fixes the coset `eN = N`. So `H_e := H_N` and its orthogonal complement
  (the sum of the `H_c` with `c != N`) are both `rho(N)`-invariant.
- Hence `P_(H_e) in rho(N)'`.
- The map `f -> f(e)` is a unitary `H_e -> H`: `f` is determined on `N` by
  `f(n) = sigma(n)^(-1) f(e)`, and `||f||^2 = ||f(e)||^2`.
- For `m in N` and `f in H_e`:
  `(rho(m) f)(e) = f(m^(-1)) = sigma(m) f(e)`.
  So `rho|_N` restricted to `H_e` is unitarily equivalent to `sigma`.

**Consequence.** By Step 0, `F_rho P_(H_e) = P_(H_e) F_rho`. This is the
projection onto `Fix rho(N) intersect H_e`, which corresponds to `Fix sigma(N)`.
So if `sigma` has no nonzero invariant vector, then `F_rho eta = 0` for every
`eta in H_e`.

**Coefficients.** For `xi in H`, let `eta in H_e` be the vector with
`eta(e) = xi`. Then:
- for `gamma in N`: `<rho(gamma) eta, eta> = <sigma(gamma) xi, xi>`;
- for `gamma notin N`: `rho(gamma) eta` is supported on `gamma N != N`, so
  `<rho(gamma) eta, eta> = 0`.

## Step 2: the quasi-regular coset vector

Let `lambda = lambda_(Gamma/N)` and `delta = delta_(eN)`.
- `<lambda(gamma) delta, delta>` equals `1` if `gamma in N` and `0` otherwise.
- `delta` is fixed by `lambda(N)`.

## Step 3: contradiction

Let `x` satisfy (G1) and (G2) with constant `epsilon > 0`, and suppose `N` does
not have (T).

**Choice of vectors.** By definition there is a unitary representation `sigma` of
`N` on `H` with no nonzero invariant vector and with almost invariant vectors.
- `N` is countable. Enumerate it and pick unit vectors `xi_k` with
  `||sigma(n_j) xi_k - xi_k|| < 1/k` for `j <= k`.
- Then `<sigma(n) xi_k, xi_k> -> 1` for every `n in N`.
- Let `rho = Ind sigma`, and let `eta_k in H_e` be the unit vectors with
  `eta_k(e) = xi_k`.

**Convergence of states.** Define the states
`omega_k(y) = <rho(y) eta_k, eta_k>` and `omega(y) = <lambda(y) delta, delta>` on `C*(Gamma)`.
- By Steps 1 and 2, `omega_k(gamma) -> omega(gamma)` for every `gamma in Gamma`.
- Hence `omega_k -> omega` on `C[Gamma]`, by linearity.
- Hence `omega_k -> omega` on all of `C*(Gamma)`: states have norm `1`, and
  `C[Gamma]` is dense.

**Limit side.** By (G1) for `lambda`, `lambda(x) delta = delta`. So `omega(x) = 1`.

**Approximating side.**
- By Step 1, `F_rho eta_k = 0`, so `eta_k in (Fix rho(N))^perp`.
- `rho(x)` is self-adjoint and fixes `Fix rho(N)` pointwise by (G1). So it
  preserves `(Fix rho(N))^perp`.
- By (G2), `|omega_k(x)| = |<rho(x) eta_k, eta_k>| <= 1 - epsilon`.

**Contradiction.** Letting `k -> infinity` gives `1 <= 1 - epsilon`. So `N` has
(T). QED

**Refinement.** The argument used (G1) and (G2) only for `lambda` and for
`Ind sigma` with the chosen `sigma`. This proves the class-restricted form.

## Step 4: the universal projection and the converse

- If `rho(p) = F_rho` for all `rho`, then (G1) holds, and (G2) holds with
  `epsilon = 1`, because `rho(p) = 0` on `(Fix rho(N))^perp`.
- Conversely, suppose `N` has (T).
  - The classical Kazhdan projection `p_N in C*(N)` satisfies
    `pi(p_N) = F_pi` for every representation `pi` of `N`.
    Reference: Akemann–Walter; Valette, "Minimal projections, integrable
    representations and property (T)", Arch. Math. 43 (1984).
  - The inclusion `C*(N) -> C*(Gamma)` is injective for discrete groups, since
    every representation of `N` embeds in the restriction of its induced
    representation.
  - So `p_N` is a universal N-fixed projection in `C*(Gamma)`.
- The converse is not used by the kill.

## Step 5: why the class members fall under the theorem

- **Relative (T) of `(Gamma,N)` does not give such an `x`.**
  - A relative (T) pair with `N` non-Kazhdan exists, for example
    `Z^2 <= Z^2 x| SL_2(Z)`.
  - A relative Kazhdan projection in `C*(Gamma)` would be a universal
    N-fixed projection. By the theorem it would make `Z^2` Kazhdan, which is false.
- **Uniform relative Kesten gap.** This is an element of `C[Gamma]` that fixes
  `Fix(N)` pointwise and has spectral radius at most `1 - epsilon` on the
  complement, in every representation. That is exactly (G1) and (G2).
- **Norm limits and functional calculus.** These stay in `C*(Gamma)`.
  Conversely, let `x` be a self-adjoint contraction satisfying (G1) and (G2), and
  let `phi` be continuous with `phi(1) = 1` and `phi = 0` on `[-1, 1-epsilon]`.
  Then `phi(x)` is a universal projection. So the two forms are equivalent.
- **Transport in the corona.** Any such element `x` is pushed into each model's
  adjoint corona `B` through `sigma~: C*(Gamma) -> B`. So a model-independent
  transport certificate is an element as in the theorem.
- **Model-dependent certificates.** A certificate valid only on corona
  representations of MF models is not covered unless that class contains the
  induced limits of the refinement. This is the one remaining admissible shape.
