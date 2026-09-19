---
rg: 2
id: fpbs-free-product-commuting-quotients-identity-e-proof
kind: route
title: Cut vertices of the block tree factor the two-point function, commuting images turn the fibre sum into a resolvent of one symmetric kernel, and the diagonal formula plus strict monotonicity close the gap between the two thresholds
target: fpbs-free-product-commuting-quotients-satisfy-identity-e
requires:
  - fpbs-quotient-l2-threshold-sandwich
  - fpbs-hp-relative-sharpness
---

Complete written proof. No computation is used. Notation as in the target.
Every function below is nonnegative, so every sum and convolution is
rearranged freely in `[0,infinity]`.

**Imports.**

- `fpbs-quotient-l2-threshold-sandwich` (ESTABLISHED): the norm `||.||_Q`,
  part 4 (`p^Q_(2->2)(N;G) <= p_c(N;G)`) and part 6 (the critical form).
- `fpbs-hp-relative-sharpness` (ESTABLISHED, imported from Hutchcroft--Pan):
  `E_p|K_o ∩ N| < infinity` for `p < p_c(N;G)`.
- **Kesten's theorem** for a symmetric probability measure `mu` on a
  countable group `Q` whose support generates `Q`:
  `||lambda_Q(mu)|| < 1` iff `Q` is nonamenable. See Woess, *Random walks on
  infinite graphs and groups*, Cor. 12.5, with `||lambda(mu)|| = rho(mu)` for
  symmetric `mu`.
- **Amenable norm.** For `f >= 0` on an amenable group, `||f||_Q = ||f||_1`.
  Test `<1_F, f * 1_F>/|F|` on Folner sets `F` against finite truncations of `f`.
  The bound `||f||_Q <= ||f||_1` is Young's inequality, valid on every group.
- **Norm calculus.** For `u, v >= 0` on `Q`:
  - `||u * v||_Q <= ||u||_Q ||v||_Q`;
  - `||u + v||_Q <= ||u||_Q + ||v||_Q`;
  - `u <= v` pointwise implies `||u||_Q <= ||v||_Q`;
  - `||u * delta_q||_Q = ||u||_Q`.

  All four follow from the sup definition over nonnegative finitely supported
  vectors.

## Step 1. The two-point function factors over the normal form

Every `g in Gamma` has a unique normal form `g = g_1 g_2 ... g_n`, with the
letters alternately in `A \ {e}` and `H \ {e}`. Put `x_i = g_1 ... g_i`, so
`x_0 = o`.

**Blocks.** A block is a left coset `yA` or `yH`. It spans a copy of
`Cay(A,S_A)` or `Cay(H,S_H)`. The edge `{y, ys}` lies in the block `yA` if
`s in S_A` and in `yH` if `s in S_H`, so the blocks partition the edges.

**The block tree.** The Bass--Serre tree `T` of `A * H` has:

- vertex set `Gamma/A ⊔ Gamma/H`;
- one edge for each `y in Gamma`, joining `yA` and `yH`.

A vertex `y` of `G` lies in exactly the two blocks at the ends of the tree edge
`y`.

**(1a) Separation.** Removing the tree edge `y` splits `T` into two sides.
Every `G`-vertex other than `y` lies in blocks on one side only. A `G`-edge
lies in one block, so it joins two vertices on the same side or meets `y`.
So `y` is a cut vertex of `G`: vertices on different sides of the tree edge
`y` lie in different components of `G - y`.

- The tree geodesic from edge `o` to edge `g` crosses exactly the edges
  `x_0, ..., x_n`.
- So for `0 < i < n`, the vertex `x_i` separates `x_(i-1)` from `x_(i+1)`
  in `G`.

**(1b) Simple paths inside a block stay in it.** A simple path in `G` between
two vertices of a block `C` stays in `C`. If it left `C` at a vertex `v` into
another block, it would lie on the far side of the tree edge `v` from `C`, and
could return only through `v` again.

**(1c) Factorisation.** Take any open simple path from `o` to `g`.

- By (1a) it visits `x_1, ..., x_(n-1)` in order.
- By (1b) the segment from `x_(i-1)` to `x_i` lies in the block `C_i`
  containing both.

So `{o <-> g} = ∩_i {x_(i-1) <-> x_i inside C_i}`. The blocks are
edge-disjoint, so these events are independent. Left translation by
`x_(i-1)` maps `C_i` onto the factor graph. Hence

```text
tau_p(o,g) = prod_(i=1)^n tau^(F_i)_p(e, g_i),     F_i in {A, H} the factor of g_i.
```

## Step 2. The renewal formula (part 1)

Suppose a normal form has `k` letters `a_1, ..., a_k` from `A` and `l` letters
`h_1, ..., h_l` from `H`, so `|k - l| <= 1`.

Since `pi(A)` and `pi(H)` commute,
`pi(g) = pi(a_1)...pi(a_k) pi(h_1)...pi(h_l)`. Summing Step 1 over all
letters of a fixed pattern gives `alpha^(*k) * beta^(*l)`. The number of
patterns with counts `(k,l)` is:

- one for `k = l = 0`;
- two for `k = l >= 1` (starting with `A` or with `H`);
- one for `|k - l| = 1`.

So

```text
sigma^N_p = delta_e + 2 sum_(k>=1) alpha^k beta^k
            + sum_(k>=0) ( alpha^(k+1) beta^k + alpha^k beta^(k+1) ).
```

Here powers are convolution powers, and `alpha * beta = beta * alpha` because
the supports commute elementwise. Expanding
`(delta_e + alpha)(delta_e + beta) sum_(j>=0) (alpha beta)^j` gives the same
coefficients, which is part 1.

`f = alpha * beta` is symmetric because `alpha` and `beta` are:
`tau(e,a) = tau(e,a^(-1))`, and `(ab)^(-1) = a^(-1) b^(-1)` in `Q`. In
particular

```text
(2.1)   sigma^N_p  >=  sum_(k>=0) f_p^(*k)   pointwise,
(2.2)   ||sigma^N_p||_Q  <=  (1 + ||alpha_p||_Q)(1 + ||beta_p||_Q) sum_(k>=0) ||f_p||_Q^k.
```

## Step 3. Diagonal lemma

**Lemma D.** Let `f >= 0` be symmetric on a countable group `Q`. Then
`limsup_k (f^(*2k)(e))^(1/2k) = ||f||_Q` in `[0,infinity]`.

*Proof.*

- If some `f(q) = infinity`, both sides are infinite, since
  `f^(*2)(e) >= f(q) f(q^(-1))`. So assume `f` is finite.
- **Upper bound.** If `||f||_Q < infinity`, then `lambda(f)` is bounded and
  self-adjoint, and `f^(*2k)(e) = <delta_e, lambda(f)^(2k) delta_e>` is at most
  `||f||_Q^(2k)`.
- **Lower bound.** Let `f_n = f 1_(B_n)` for finite symmetric sets `B_n`
  increasing to `Q`. Then `lambda(f_n)` is bounded and self-adjoint.
  - Its spectral measure `mu_n` at `delta_e` has support equal to the whole
    spectrum. If `E(U) delta_e = 0` for a spectral projection `E(U)`, then
    `E(U)` commutes with right translations `rho(q)`. So
    `E(U) delta_q = rho(q) E(U) delta_e = 0` for every `q`, and `E(U) = 0`.
  - Hence `lim_k (f_n^(*2k)(e))^(1/2k) = max|spec lambda(f_n)| = ||f_n||_Q`.
  - Since `f_n <= f`, this gives `limsup_k (f^(*2k)(e))^(1/2k) >= ||f_n||_Q`.
  - Finally `||f_n||_Q` increases to `||f||_Q`: each pairing `<g, f_n * h>`
    with finitely supported `g, h >= 0` is a finite sum and increases to
    `<g, f * h>`. ∎

## Step 4. Strict monotonicity

**Lemma M.** Let `X` be a graph in which the vertex `o` has degree `d`, and
let `0 < p < p' <= 1`. Put `c = 1 - (1 - p/p')^d < 1`. Then
`P_p(o <-> x) <= c P_(p')(o <-> x)` for every `x ≠ o`.

*Proof.* Couple `omega_p = omega_(p') ∩ xi`, with `xi` an independent
Bernoulli(`p/p'`) edge field. Since `x ≠ o`, `{o <-> x in omega_p}` needs
`o <-> x` in `omega_(p')` and some `omega_(p')`-open edge at `o` kept by `xi`.
Given `omega_(p')`, the second event has probability at most `c`. ∎

Apply this in the factor graphs, with `c_A` for degree `|S_A|` and `c_H` for
degree `|S_H|`. Only `a ≠ e` and `h ≠ e` enter `alpha` and `beta`, so
`alpha_p <= c_A alpha_(p')` and `beta_p <= c_H beta_(p')`. Therefore

```text
(4.1)   f_p <= c_A c_H f_(p')   pointwise,   and   ||f_p||_Q <= c_A c_H ||f_(p')||_Q.
```

For `s in S_H` we have `beta_p(pi(s)) >= tau^H_p(e,s) >= p`, so
`f_p >= p (alpha_p * delta_(pi(s)))`. Hence, for `p > 0`,

```text
(4.2)   ||alpha_p||_Q <= ||f_p||_Q / p,        and symmetrically ||beta_p||_Q <= ||f_p||_Q / p.
```

## Step 5. Claim E on the class (part 2)

Put `p* = sup{p : ||f_p||_Q < 1}`.

**(a) `p* <= p^Q_(2->2)(N;G)`.** Suppose `p > 0` and `||f_p||_Q < 1`. By (4.2)
`alpha_p` and `beta_p` have finite norms, so (2.2) gives
`||sigma^N_p||_Q < infinity`.

**(b) `p_c(N;G) <= p*`.** Take `p < p' < p_c(N;G)`.

- By relative sharpness, `sigma^N_(p')(e) = E_(p')|K_o ∩ N| < infinity`.
- By (2.1), `sum_k f_(p')^(*k)(e) < infinity`, so `f_(p')^(*2k)(e) -> 0`.
- By Lemma D, `||f_(p')||_Q <= 1`.
- By (4.1), `||f_p||_Q <= c_A c_H < 1`, so `p <= p*`.

**(c)** Part 4 of the sandwich gives `p^Q_(2->2)(N;G) <= p_c(N;G)`.

Together these give `p* <= p^Q_(2->2)(N;G) <= p_c(N;G) <= p*`. ∎

**Trivial quotient.** Steps 1, 2, 4 and 5 hold verbatim for `N = Gamma`, with
`Q` trivial.

- There `||f_p||_Q = ||f_p||_1 = (chi^A_p - 1)(chi^H_p - 1)`, and
  `p_c(Gamma;G) = p_c(G)`.
- This recovers Kozáková's formula for `p_c(A * H)`.
- Since `(chi^A_p - 1)(chi^H_p - 1)` is strictly increasing by (4.1),
  `p_c(G)` is its root.

**Special cases of the target.**

- If `N = <<A>>`, then `pi(A) = {e}` and `alpha_p = (chi^A_p - 1) delta_e`.
- If `N = [A,H]`, then `Q = A x H` and `f_p` is the tensor product
  `(tau^A_p - delta) ⊗ (tau^H_p - delta)`. So `||f_p||_Q` is the product of
  the two factor norms.
- In both cases `||tau_p - delta_e||_F = ||T^F_p|| - 1`. The operator of
  `tau_p - delta_e` is self-adjoint with a nonnegative kernel, so its norm is
  the top of its spectrum.

## Step 6. The Kesten gap (part 3)

**Amenable `Q`.** For every `p`,
`||f_p||_Q = ||f_p||_1 = (chi^A_p - 1)(chi^H_p - 1)`. So `p* = p_c(G)`, and by
part 2 `p_c(N;G) = p_c(G)`.

**Nonamenable `Q`.** Put `p_0 = p_c(G)`. Then `p_0 > 0`, because `G` is
locally finite.

*Norms at `p_0` are finite.*

- Each `tau^F_p(e,x)` is left-continuous in `p`: it is an increasing supremum
  over `n` of the continuous functions `P_p(e <-> x inside the ball B_n)`. So
  `chi^A_p` and `chi^H_p` are left-continuous by monotone convergence.
- For `p < p_0` the trivial-quotient case gives
  `(chi^A_p - 1)(chi^H_p - 1) < 1`. So `||f_(p_0)||_1 <= 1`.
- Both factors are at least `p_0 > 0`, so `||alpha_(p_0)||_1` and
  `||beta_(p_0)||_1` are finite.

*Kesten's theorem applies.* Let `mu = f_(p_0) / ||f_(p_0)||_1`, a symmetric
probability measure on `Q`. Its support is `pi(A \ {e}) pi(H \ {e})`, because
the factor graphs are connected and `p_0 > 0`. We show this support generates
`Q`.

- Since `A` and `H` are not both of order 2, we may assume `|H| >= 3`.
- Every `t in H \ {e}` is `h h'^(-1)` with `h, h' in H \ {e}`: choose
  `h' notin {e, t^(-1)}` and `h = t h'`.
- Then `pi(a)pi(h) (pi(a)pi(h'))^(-1) = pi(h h'^(-1))`, because the images
  commute. So `pi(H)` lies in the generated subgroup.
- Also `pi(a) = (pi(a)pi(h)) pi(h)^(-1)` lies in it. Hence the subgroup
  contains `pi(A) pi(H) = Q`.

Kesten's theorem gives `||lambda_Q(mu)|| < 1`, so
`||f_(p_0)||_Q < ||f_(p_0)||_1 <= 1`.

*Conclusion.* Young's inequality gives `||alpha_(p_0)||_Q <= ||alpha_(p_0)||_1`,
and the same for `beta`. So (2.2) gives `||sigma^N_(p_0)||_Q < infinity`, the
critical fibre l2 condition. Part 6 of the sandwich then gives
`p_c(G) < p^Q_(2->2)(N;G) = p_c(N;G)`. ∎

## Where the method stops

The proof uses only the renewal identity of Step 2. That identity needs two
things.

- **Cut vertices.** Step 1 needs blocks that meet in single vertices. For an
  amalgam `A *_C H` with `C ≠ 1`, blocks meet in copies of `C` and the
  two-point function does not factor. Infinite amenable `C` is the case where
  C2 of `fpbs-relative-threshold-is-quotient-l2-threshold` has content.
- **Commuting images.** Step 2 needs `pi(A)` and `pi(H)` to commute, so that
  every alternating word collapses to `alpha^k beta^l`. For a general normal
  `N` of `A * H` the fibre sum is a sum over alternating words in two
  non-commuting kernels. Its e-value and its norm are then no longer
  functions of one symmetric kernel, and Lemma D does not compare them.

These are the two open directions from this node.
