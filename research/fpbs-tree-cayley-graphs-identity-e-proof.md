---
rg: 2
id: fpbs-tree-cayley-graphs-identity-e-proof
kind: route
title: The tree Green identity makes the two-point function a Green function on the group, its pushforward is a resolvent of the quotient walk, and the resolvent's spectrum and diagonal pin both thresholds at the same point
target: fpbs-tree-cayley-graphs-satisfy-identity-e
requires:
  - fpbs-quotient-l2-threshold-sandwich
  - fpbs-hp-relative-sharpness
---

Complete written proof. No computation is used. Notation as in the target.
All functions are nonnegative, so sums are rearranged freely in
`[0,infinity]` (Tonelli).

**Imports.**

- `fpbs-quotient-l2-threshold-sandwich` (ESTABLISHED): the norm `||.||_Q`
  and part 4, `p^Q_(2->2)(N;G) <= p_c(N;G)` for infinite normal `N`.
- `fpbs-hp-relative-sharpness` (ESTABLISHED, imported): `E_p|K_o ∩ N| < infinity`
  for `p < p_c(N;G)`. Contrapositive: `chi^N_p = infinity` forces
  `p >= p_c(N;G)`.
- **Kesten.** For a symmetric probability `nu` on a countable group `R`
  whose support generates `R`:
  (K1) `||lambda_R(nu)|| = limsup_k nu^(*k)(e)^(1/k) =: rho(nu)`;
  (K2) if `M` is a normal subgroup of `R`, then
  `rho(pi_* nu) = rho(nu)` iff `M` is amenable;
  (K3) for simple random walk on the `(q+1)`-regular tree,
  `rho = 2 sqrt q/(q+1)`.
  Kesten 1959 (Trans. AMS 92 and Math. Scand. 7); see Woess, *Random walks
  on infinite graphs and groups*, Sections 1 and 12. Imported, not
  re-proved.
- Elementary facts on free groups: centralisers of nontrivial elements are
  cyclic; amenable subgroups are cyclic.

## Step 0. Infinite normal subgroups are nonamenable, so `rho_Q > rho_T`

`Gamma` acts on `T` by left multiplication, freely and transitively on
vertices. Every edge stabiliser has order at most 2 (an edge `{g, gs}` with
`s^2 = e` may be inverted). After barycentric subdivision the action has no
inversions, finite stabilisers and finite quotient graph. By Bass--Serre
theory, `Gamma` is the
fundamental group of a finite graph of finite groups, hence virtually free.
Let `F` be a free normal subgroup of finite index. `F` is quasi-isometric to
`T`, which has infinitely many ends because `q >= 2`, so `F` has rank at
least 2.

Suppose `N` is infinite and amenable. Then `N ∩ F` has finite index in `N`,
so it is infinite. It is amenable, so it is cyclic, say `<c>` with `c != e`.
It is normal in `F`, so each `f in F` sends `c` to `c^(±1)`. The kernel `F_0`
of the resulting map `F -> Aut(Z) = Z/2` has index at most 2 in `F`, so it is
free of rank at least 2. But `F_0` centralises `c`, and the centraliser of
`c` in `F` is cyclic. This is a contradiction. So `N` is nonamenable.

By (K2) applied to `R = Gamma`, `nu = mu` and `M = N`, and by (K3) (since
`mu^(*k)(e)` is the `k`-step return probability of simple random walk on `T`),
we get `rho_Q > rho(mu) = 2 sqrt q/(q+1)`.

## Step 1. The pointwise tree Green identity

Let `X_k = s_1 ... s_k` with `s_i` i.i.d. of law `mu`. The neighbours of `g`
in `T` are the `gs`, `s in S`, so `X` is simple random walk on `T` started
at `e`, and `mu^(*k)(x) = P(X_k = x)`. For `w >= 0` put
`G_w(e,x) = sum_k w^k mu^(*k)(x)`.

Let `F(w)` be the generating function of the first hitting time of a fixed
neighbour. It is the same for every neighbour, since the automorphism group
of `T` is transitive on directed edges and simple random walk depends only on
the graph. A first step either goes to the target (probability `1/(q+1)`),
or goes away, after which the walk must cross two edges towards the target.
So

```text
F = w/(q+1) + (q w/(q+1)) F^2 .
```

Since `F(0) = 0` and `F` is continuous and nondecreasing wherever it is
finite, `F(w)` is the smaller root.

Now fix `s in [0, 1/sqrt q]` and put `w = w(s) = (q+1) s/(1+q s^2)`. Then `s`
is a root:

```text
w/(q+1) + (q w/(q+1)) s^2 - s = z(s)(1 + q s^2) - s = 0 .
```

The product of the roots is `1/q`, so the other root is `1/(q s) >= 1/sqrt q >= s`.
Hence `F(w(s)) = s`.

The unique geodesic from `e` to `x` must be crossed edge by edge. By the
strong Markov property at the successive first hitting times,
`G_w(e,x) = F(w)^|x| G_w(x,x) = F(w)^|x| G_w(e,e)`. A first return is a step
followed by a first hit of `e`, so `G_w(e,e) = 1/(1 - w F(w))`. At
`w = w(s)`,

```text
1 - w(s) s = 1 - (q+1) s^2/(1+q s^2) = (1-s^2)/(1+q s^2) = phi(s) > 0 .
```

Therefore, for every `x in Gamma` and `s in [0, 1/sqrt q]`,

```text
s^|x| = phi(s) sum_(k>=0) w(s)^k mu^(*k)(x) ,       (1)
```

with both sides finite.

## Step 2. Resolvent form (item 1)

On a tree `tau_p(o,x) = p^|x|`, since the geodesic is the only path and its
edges are open independently. For `p in [0, 1/sqrt q]`, sum (1) over the
coset `u = pi(x)` and use `pi_*(mu^(*k)) = mu_Q^(*k)` (as `pi` is a
homomorphism):

```text
sigma_p(u) = phi(p) sum_k w(p)^k mu_Q^(*k)(u) .
```

## Step 3. The norm (item 2)

Put `A = lambda_Q(mu_Q)`, the operator `h -> mu_Q * h` on `l2(Q)`. It is
self-adjoint because `mu_Q` is symmetric, and `||A|| = rho_Q` by (K1).

*The top of the spectrum is `rho_Q`.* For self-adjoint `A`,
`max spec(A) = sup_(||g||=1) <g,Ag>`. The kernel of `A` is nonnegative, so
`|<g,Ag>| <= <|g|, A|g|>` and `sup_(g>=0, ||g||=1) <g,Ag> = ||A|| = rho_Q`.
Hence `max spec(A) >= rho_Q`, and so `rho_Q in spec(A)`.

*The norm `||.||_Q` is the operator norm.* For a kernel `f >= 0` and any
`g, h`, `|<g, f*h>| <= <|g|, f*|h|>`. So, when `lambda_Q(f)` is bounded,
`||f||_Q = ||lambda_Q(f)||`.

*The existence of `s_N`.* On `[0, 1/sqrt q]` the map `w` is continuous and
strictly increasing (`w'(s)` has the sign of `1 - q s^2`), with `w(0) = 0`
and `w(1/sqrt q) = (q+1)/(2 sqrt q) = 1/rho_T`. By Step 0,
`1/rho_Q < 1/rho_T`, so `w(s) rho_Q = 1` has exactly one solution
`s_N in (0, 1/sqrt q)`.

*Case `p < s_N`.* Here `w(p) rho_Q < 1`, and
`B = phi(p) sum_k w^k A^k = phi(p)(1 - wA)^(-1)` converges in norm. It is
self-adjoint, with spectrum `{phi/(1 - w t) : t in spec(A)}`. Since
`spec(A) ⊂ [-rho_Q, rho_Q]` contains `rho_Q`, this gives
`||B|| = phi(p)/(1 - w(p) rho_Q)`. By Step 2, `B = lambda_Q(sigma_p)`, so
`||sigma_p||_Q = phi(p)/(1 - w(p) rho_Q)`.

*Case `s_N <= p <= 1/sqrt q`.* Here `w rho_Q >= 1`. Fix `eps > 0` and a
finitely supported `g >= 0` with `||g|| = 1` and `<g,Ag> >= rho_Q - eps`. Let
`nu_g` be its spectral measure, a probability measure on `[-rho_Q, rho_Q]`.
Then:

- every term `<g, mu_Q^(*k) * g>` is `>= 0`;
- for even `k = 2j`, Jensen gives
  `<g, A^(2j) g> = ∫ t^(2j) d nu_g >= (∫ t d nu_g)^(2j) >= (rho_Q - eps)^(2j)`.

Hence

```text
<g, sigma_p * g>  >=  phi(p) sum_j (w (rho_Q - eps))^(2j) .
```

If `w rho_Q > 1`, choose `eps` with `w(rho_Q - eps) >= 1`; the sum is
infinite. If `w rho_Q = 1`, the sum is `phi/(1 - (1 - w eps)^2)`, which tends
to infinity as `eps -> 0`. Either way `||sigma_p||_Q = infinity`.

*Case `p > 1/sqrt q`.* `tau_p` is nondecreasing in `p`, so `||sigma_p||_Q`
is too, and it is infinite.

## Step 4. Identity E (item 3)

By Step 3, `{p : ||sigma_p||_Q < infinity} = [0, s_N)`, so
`p^Q_(2->2)(N;T) = s_N`.

For `p in (s_N, 1/sqrt q]`, Step 2 at `u = e` gives
`chi^N_p = sigma_p(e) = phi(p) sum_k w(p)^k mu_Q^(*k)(e)`. By (K1), the
radius of convergence of this series is `1/rho_Q < w(p)`, so
`chi^N_p = infinity`. By monotonicity, `chi^N_p = infinity` for every
`p > s_N`. By relative sharpness, every such `p` is `>= p_c(N;T)`, so
`p_c(N;T) <= s_N`.

By part 4 of the sandwich, `s_N = p^Q_(2->2)(N;T) <= p_c(N;T)`. Hence
`p_c(N;T) = p^Q_(2->2)(N;T) = s_N`.

## Step 5. Type and endpoint (items 4 and 5)

`p_c(T) = 1/q`, and `w(1/q) = (q+1)(1/q)/(1 + 1/q) = 1`. Since `w` is
strictly increasing, `p_c(T) < s_N` iff `w(p_c) rho_Q < 1` iff `rho_Q < 1`.
By Kesten's amenability criterion (K2 with `M = Q`, or directly
`rho_Q < 1` iff `Q` nonamenable), this holds iff `Q` is nonamenable. If
`Q` is nonamenable, `p_c < s_N = p^Q_(2->2)`, which is type (i). If `Q` is
amenable, `s_N = p_c = p_c(N;T)`, which is type (iii). Type (ii) would need
`p^Q_(2->2) < p_c(N;T)`, which Step 4 excludes.

At `p = s_N`, Step 2 gives
`chi^N_(s_N) = phi(s_N) sum_k rho_Q^(-k) mu_Q^(*k)(e) = phi(s_N) G_Q(1/rho_Q)`,
which is finite iff `mu_Q` is rho-transient. Step 3 gives
`||sigma_(s_N)||_Q = infinity`. For `p < s_N`,
`||sigma_p||_Q = phi(p)/(1 - w(p) rho_Q)`, and `w'(s_N) > 0`, so the norm is
of order `(s_N - p)^(-1)` as `p ↑ s_N`. ∎

## Consistency checks

- For `F_d` on a free basis, Step 4 gives `p_c(N;T) = s_N`, the value in
  item 2 of `fpbs-tree-normal-relative-threshold-is-inverse-cogrowth`. That
  node proves it by a different argument (a branching process of cyclically
  reduced blocks), so the two proofs check each other. The two values of
  `chi^N_(s_N)` agree as well (item 3 there).
- For `N = [Gamma,Gamma]` in `F_2` we have `Q = Z^2` and `rho_Q = 1`, so
  `s_N = 1/3 = p_c`: no gap, as required by C3.
- The `(q+1)`-regular tree with `q+1 = 3` arises from `(Z/2)^{*3}` and from
  `Z * Z/2`. The theorem treats both at once, because (1) depends only on the
  graph.
