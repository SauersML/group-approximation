---
rg: 2
id: fpbs-fibre-renormalized-nonbacktracking-certificate-proof
kind: route
title: BK over fibre segments gives a backtrack-weighted word count, a Woodbury reduction on directed quotient edges makes it a scalar quadratic, and Pringsheim converts invertibility along a segment into convergence
target: fpbs-fibre-renormalized-nonbacktracking-certificate
requires: []
---

Notation as in the target. The imported standard results are:

* the van den Berg–Kesten (BK) inequality;
* the Harris–FKG inequality;
* `p_c = p_T` on transitive graphs (Menshikov; Aizenman–Barsky);
* monotonicity of uniqueness on Cayley graphs (Häggström–Peres; Schonmann);
* Pringsheim's theorem: a power series with nonnegative coefficients and
  radius of convergence `R < infinity` has a singular point at `z = R`;
* the identity `I - UV` invertible iff `I - VU` invertible, for bounded `U, V`.

Throughout, `p < 1`, `chi = chi_N(p) < infinity`, `gamma = 1/chi`,
`beta = 1 - gamma = (chi-1)/chi` and `t = p chi`, so `gamma t = p < 1`. Write
`tau_N(u,v)` for the probability that `u` and `v` are joined by an open path
using only `S_N`-edges. The `S_N`-subgraph through `u` is a translate of
`Cay(<S_N>,S_N)`, so

```text
sum_v tau_N(u,v) = chi,    sum_{v != u} tau_N(u,v) = chi - 1.
```

Since `S_N ⊂ N` and `N` is normal, an `S_N`-edge `{y, ys}` stays in the coset
`yN`, while an `S'`-edge `{y, ys}` moves `yN` to `y s N`, i.e. `pi(y)` to
`pi(y) pi(s)`.

## Step 1: BK over fibre segments

Let `x ∈ qN` with `o <-> x`. Choose an open self-avoiding path from `o` to `x`
and cut it at its `S'`-edges:

```text
sigma_0, e_1, sigma_1, e_2, ..., e_m, sigma_m,
```

where each `sigma_i` is a (possibly empty) path of `S_N`-edges from `u_i` to
`v_i`, and `e_i` is the `S'`-edge from `v_(i-1)` to `u_i = v_(i-1) s_i` with
`s_i ∈ S'`. Then `u_0 = o`, `v_m = x`, and the coset of `x` is
`pi(s_1) ... pi(s_m) = q`.

**No trivial backtracks.** Suppose `1 <= i <= m-1`, `sigma_i` is empty (so
`v_i = u_i`) and `s_(i+1) = s_i^(-1)`. Then `u_(i+1) = v_(i-1)`, and the path
revisits a vertex, which is impossible. So whenever `s_(i+1) = s_i^(-1)`, the
segment `sigma_i` has `v_i != u_i`.

**BK.** The segments and edges use pairwise disjoint edge sets. The event
`{o <-> x}` is therefore contained in the union, over `m`, over labels
`s_1, ..., s_m` and over the vertices `v_0, ..., v_(m-1)` (with `v_i != u_i`
at the backtrack positions), of the disjoint occurrence

```text
{u_0 <->_{S_N} v_0} ∘ {e_1 open} ∘ {u_1 <->_{S_N} v_1} ∘ ... ∘ {e_m open} ∘ {u_m <->_{S_N} x}.
```

These events are increasing. BK applies to them by the usual restriction to
finite edge sets and a monotone limit. The union bound then gives
`P(o <-> x) <= sum tau_N(u_0,v_0) p tau_N(u_1,v_1) p ... p tau_N(u_m,x)`.

**Summing over endpoints.** Sum over `x ∈ qN` and over `v_0, ..., v_(m-1)`,
innermost last. The final segment and the first segment each contribute
`chi`. A middle segment contributes `chi - 1 = beta chi` if
`s_(i+1) = s_i^(-1)`, and at most `chi` otherwise. With `bt(s)` the number of
indices `1 <= i <= m-1` with `s_(i+1) = s_i^(-1)`:

```text
E_p|C(o) ∩ qN|  <=  chi 1{q = e}  +  chi sum_{m >= 1} t^m W_m(q),
W_m(q) = sum_{s_1..s_m ∈ S', pi(s_1...s_m) = q}  beta^{bt(s)}.        (1)
```

The factor count for `m >= 1` is `chi^2 chi^(m-1) p^m = chi t^m`.

## Step 2: directed quotient edges

Assume `d' >= 1`. (If `d' = 0` then `W_m = 0` for `m >= 1` and (1) is `chi`.)
On `V = l2(Q × S')` let

```text
(P f)(q,s) = sum_{s' ∈ S'} w(s,s') f(q pi(s'), s'),   w(s,s') = 1 - gamma 1{s' = s^(-1)}.
```

`P` is a nonnegative matrix whose row sums are `d' - gamma`, so it is bounded.
A state `(q,s)` records the current coset and the last label. Put
`a = sum_s delta_(pi(s),s)` and `b_q = sum_s delta_(q,s)`. Both are finitely
supported. Following the labels one at a time,

```text
W_m(q) = < a, P^(m-1) b_q >   (m >= 1),                            (2)
```

and `c_n = <a, P^n b_q> >= 0`.

**Operator identities.** Define

* `R: l2(Q) -> V`, `(R g)(q,s) = g(q)`;
* `E: V -> l2(Q)`, `(E f)(q) = sum_{s'} f(q pi(s'), s')`;
* `J: V -> V`, `(J f)(q,s) = f(q pi(s)^(-1), s^(-1))`.

`J` permutes the basis: it maps `delta_(q,s)` to
`delta_(q pi(s), s^(-1))`, and applying it twice returns `delta_(q,s)`. So
`J^2 = I` and `||J|| = 1`. The following identities hold:

* `P = R E - gamma J`.
* `E J = R*`, because
  `(E J f)(q) = sum_{s'} f(q pi(s') pi(s')^(-1), s'^(-1)) = sum_s f(q,s) = (R* f)(q)`.
* `E R = A_X`, because `(E R g)(q) = sum_{s'} g(q pi(s'))`.
* `R* R = d' I`.

`A_X` is self-adjoint because `S'` is symmetric.

## Step 3: Woodbury reduction

Let `0 <= z <= t`. Then `gamma z <= p < 1`, so `I + gamma z J` is invertible
with inverse `(I - gamma z J)/(1 - gamma^2 z^2)`. Write

```text
I - z P = (I + gamma z J) - z R E = (I + gamma z J)(I - z (I + gamma z J)^(-1) R E).
```

By `I - UV` invertible iff `I - VU` invertible (take `U = z (I+gamma z J)^(-1) R`
and `V = E`), `I - zP` is invertible iff `I - z E (I + gamma z J)^(-1) R` is
invertible on `l2(Q)`. By Step 2,

```text
E (I - gamma z J) R = A_X - gamma z R* R = A_X - gamma z d' I,
```

so the condition is that

```text
(1 - gamma^2 z^2) I - z (A_X - gamma z d' I)  =  (1 + gamma (d' - gamma) z^2) I - z A_X
```

is invertible. The spectrum of `A_X` lies in `[-||A_X||, ||A_X||]`, and
`1 + gamma(d'-gamma) z^2 >= 1 > 0` because `gamma <= 1 <= d'`. So the operator
is invertible whenever `F_p(z) = 1 + gamma(d'-gamma) z^2 - z ||A_X|| > 0`.
Hence the hypothesis of Theorem A gives: `I - zP` is invertible for every
`z ∈ [0,t]`.

## Step 4: Pringsheim, then Theorem A

**Convergence at `t`.** Let `g(z) = sum_n c_n z^n` with `c_n = <a, P^n b_q> >= 0`,
and let `R_0` be its radius of convergence. The set
`U = {z ∈ C : I - zP invertible}` is open, and `g_U(z) = <a, (I - zP)^(-1) b_q>`
is holomorphic on `U`. For `|z| < 1/||P||` the Neumann series gives
`g = g_U`.

By Step 3, `[0,t] ⊂ U`. Being compact, it has an open convex
`epsilon`-neighbourhood `V ⊂ U`. Suppose `R_0 <= t`.

1. `D = {|z| < R_0}` and `V` are convex, so `D ∩ V` is convex, hence connected,
   and it contains a neighbourhood of `0`.
2. `g` and `g_U` agree near `0`, so by the identity theorem they agree on
   `D ∩ V`.
3. Therefore `g` on `D` and `g_U` on `V` glue to a holomorphic function on
   `D ∪ V`, which contains a neighbourhood of `R_0 ∈ [0,t] ⊂ V`.
4. This contradicts Pringsheim's theorem.

So `R_0 > t`, and `sum_n c_n t^n < infinity`.

**Coset bound.** By (1) and (2),
`E_p|C(o) ∩ qN| <= chi + chi t sum_n c_n t^n < infinity` for every `q`.

**Consequences.**

* **Every cluster meets `N` finitely.** For any vertex `y`, translating by
  `y^(-1)` maps `C(y) ∩ N` to `C(o) ∩ y^(-1) N`. This has finite expectation,
  so it is almost surely finite. Hence almost surely every cluster meets `N` in
  finitely many vertices, and `p <= p_c(N;G)`. (The relative threshold is
  monotone in `p`, since the event is increasing.)
* **No uniqueness.** Suppose there were a unique infinite cluster at `p`. By
  Harris–FKG, `P(o <-> x) >= P(o <-> infinity, x <-> infinity) >= theta(p)^2 > 0`
  for all `x`. Summing over the infinite coset `N` would give
  `E_p|C(o) ∩ N| = infinity`, a contradiction.
* **`p <= p_u`.** By monotonicity of uniqueness, every `p' > p_u` has a unique
  infinite cluster. So `p <= p_u(G)`.

**The explicit form of the hypothesis (`d' >= 1`).** Write
`c = gamma(d'-gamma) >= 0` and `A = ||A_X|| > 0` (`A_X` is a nonzero operator).
`F_p` is convex with `F_p(0) = 1`.

* If the discriminant `A^2 - 4c < 0`, then `F_p > 0` everywhere.
* Otherwise the minimum value is `<= 0`. If `c > 0` it is attained at
  `u_* = A/(2c)`. Then `F_p > 0` on `[0,t]` iff `t < u_*` and `F_p(t) > 0`, since
  `F_p` is decreasing on `[0,u_*]`. If `c = 0`, then `F_p` is linear and
  decreasing and the condition is `F_p(t) > 0`, with `2ct < A` automatic.

This is the stated equivalence. At the boundary `t = u_*`, `F_p(t) > 0` would
force a negative discriminant.

## Step 5: Theorem B

Summing (1) over all cosets gives
`E_p|C(o)| <= chi + chi sum_{m>=1} t^m sum_q W_m(q)`. Here `sum_q W_m(q)` counts
all label words with weights. The first letter has `d'` choices. Each later
letter has `d' - 1` choices with weight `1` and one choice (`s^(-1)`) with
weight `beta`, total `d' - gamma`. So `sum_q W_m(q) = d' (d'-gamma)^(m-1)`, and
the series converges when `t (d' - gamma) < 1`, i.e.
`p chi (d' - 1/chi) = p (d' chi - 1) < 1`. Then `chi_G(p) < infinity`, so
`p <= p_T = p_c(G)`.

## Step 6: Corollary C

**Setup.** Take `Gamma = H × B`, `N = B` (normal, infinite), `S_N = S_B`,
`S' = S_H`. Then `Q = H`, `X = Cay(H,S_H)`, `A_X = A_H`, `d' = d_H >= 1`. For
`p < p_c(B) = p_T(B)`, `chi = chi_B(p) < infinity`, and `p < 1`.

**Item 1.** Let `p ∈ (p_c(G), p_c(B))`. Then `chi_G(p) = infinity`, because
`p > p_c(G) = p_T(G)`. So Theorem B's hypothesis fails:
`p chi (d_H - gamma) >= 1`. Dividing by `p chi`,
`d_H - gamma >= kappa_p`, i.e. `L_p >= 0`.

**Item 2.** Assume `p_c(G) = p_u(G)` and `p ∈ (p_c(G), p_c(B))`. Then
`p > p_u(G)`, so Theorem A's conclusion `p <= p_u(G)` is false, and its
hypothesis fails. So there is `u ∈ [0,t]` with `F_p(u) <= 0`. Since
`F_p(0) = 1`, `u > 0`, and dividing by `u`:

```text
1/u + c u <= A = d_H - delta_H,     c = gamma (d_H - gamma),  A = ||A_H||.
```

The function `phi(u) = 1/u + cu` is decreasing on `(0, u_0]` and increasing on
`[u_0, infinity)`, where `u_0 = 1/sqrt c` (`u_0 = infinity` if `c = 0`), with
`phi(u_0) = 2 sqrt c`.

* **Case `t <= u_0`.** `phi` is decreasing on `(0,t]`, so `phi(t) <= A`. Now
  `1/t = kappa_p` and `ct = gamma(d_H-gamma) p chi = p(d_H - gamma)`. So
  `kappa_p + p(d_H-gamma) <= d_H - delta_H`, which rearranges to
  `L_p = d_H - gamma - kappa_p >= delta_H - gamma + p(d_H-gamma)`. This is the
  first alternative.
* **Case `t > u_0`.** Then `ct^2 > 1`, i.e. `p(d_H - gamma) = ct > 1/t = kappa_p`.
  Also `A >= phi(u) >= phi(u_0) = 2 sqrt c`, i.e. `||A_H||^2 >= 4 gamma(d_H-gamma)`.
  This is the second alternative.

**Only `chi_B` enters.** The hypotheses and conclusions involve `B` only
through `chi_B(p)` (via `gamma`, `t`, `kappa_p`), together with the interval
endpoint `p_c(B)`.

## Step 7: the unrenormalized case

If `S_N = ∅`, then `chi = gamma = 1`, `beta = 0`, `t = p`, `d' = d` and
`c = d - 1 = b`. For `A >= 2 sqrt b`, the smaller root of
`b u^2 - A u + 1` is

```text
(A - sqrt(A^2 - 4b))/(2b) = 2/(A + sqrt(A^2 - 4b)) = 1/sigma(A).
```

So `F_p > 0` on `[0,p]` iff `p < 1/sigma(A)` (Step 4 case analysis, noting
`u_* = A/(2b) >= 1/sigma(A)`). Theorem A then gives `p_u >= 1/sigma(||A_X||)`
for infinite `N`. If `A < 2 sqrt b` it gives `p_u >= 1`.

This matches `fpbs-nb-spectral-deficit-obstruction` Theorems 1-2 with
`Lambda = max(||A_X||, 2 sqrt b)` when `||A_X|| >= 2 sqrt b`. In the other case
it is formally stronger. That case does not occur for infinite `Q`, but no
such claim is needed here. The operator `P` is the nonbacktracking operator
of `X`, and (1) is the nonbacktracking walk bound.

## Step 8: the computation

The script concerns `G_k = Cay(F_2,{a^±1,b^±1}) □ Cay(Z,{±1,...,±k})`, with
`d = 4 + 2k`.

**The label bound.** Let `c_n` be the number of self-avoiding walks of length
`n` from `o`. Then `E_p|C(o)| <= sum_n c_n p^n`, so `p_c = p_T >= 1/mu` with
`mu = lim c_n^(1/n)`.

A self-avoiding walk has label sequence `s_1 s_2 ...` with:

* `s_(i+1) != s_i^(-1)`, since it does not revisit `x_(i-1)`;
* `s_i s_(i+1) s_(i+2) != e`, since it does not revisit `x_(i-1)` after three
  steps.

In `F_2 × Z`, a product of three letters with at least one `F_2`-letter is
nontrivial. With one `F_2`-letter, the `F_2`-component is that letter. With two,
the `Z`-component is a nonzero integer. With three, the `F_2`-component has odd
length. So the script's `closes` test is exactly the triangle condition.

**The transfer bound.** `c_n` is at most the number of admissible label
sequences, which is `1^T M^(n-2) 1` over pair-states. For any positive integer
vector `v` with `M v <= lambda_* v` entrywise, `M^n v <= lambda_*^n v`, so
`1^T M^n 1 <= (#states) (max v / min v) lambda_*^n`. Hence
`mu <= lambda_*` and `D(G_k) = d - 1 - 1/p_c >= d - 1 - lambda_*`.

**Exactness.** The script computes `lambda_* = max_i (M v)_i / v_i` in exact
rational arithmetic for an integer vector `v`. The floating-point power
iteration only chooses `v`, so the bound does not depend on floating-point
error. `Delta(G_k)` is evaluated with
`Lambda = ||A_H|| + 2k = d - delta_H >= 2 sqrt(d-1)`. The Cartesian product
norm is the sum of the factor norms.
