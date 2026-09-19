---
rg: 2
id: fpbs-orbit-uniform-half-tilt-bounds-connectivity-operator-proof
kind: route
title: Cocycle factorisation turns the Radon-Nikodym square root into a Schur test function, positivity of cross terms gives the L2 gradation, and a truncated Russo-BK Riccati comparison gives openness
target: fpbs-orbit-uniform-half-tilt-bounds-connectivity-operator
requires:
  - fpbs-boundary-tilted-susceptibility-kernel
  - fpbs-quotient-l2-threshold-sandwich
  - fpbs-hutchcroft-l2-gap-criterion
---

Complete written proof. No computation is used. Notation as in the claim.

**Imports.**

- `fpbs-boundary-tilted-susceptibility-kernel` (ESTABLISHED), item 1:
  "For `nu`-a.e. `zeta` and all `x, y, w`:
  `Delta_zeta(x,y) Delta_zeta(y,w) = Delta_zeta(x,w)`;
  `Delta_(g zeta)(gx,gy) = Delta_zeta(x,y)`;
  `int Delta_zeta(o,y) d nu(zeta) = 1`." Its proof notes that every such
  identity holds simultaneously on one conull `Gamma`-invariant set, and that
  `Delta_zeta(x,y) in (0,infinity)` a.e.
- `fpbs-quotient-l2-threshold-sandwich` (ESTABLISHED), items 3 and 6: "For
  `N = {e}` the threshold is `p_(2->2)(G)`", and "`p_c(G) < p^Q_(2->2)(N;G)` iff
  `||sigma^N_(p_c)||_Q < infinity`". With `N = {e}`, `sigma^N_p = tau_p(o,.)`
  and `||sigma^N_p||_Q = ||T_p||_(2->2)`, so `p_c < p_(2->2)` iff
  `||T_(p_c)||_(2->2) < infinity`.
- `fpbs-hutchcroft-l2-gap-criterion` (ESTABLISHED), item 4: "If this holds,
  then `p_c < p_u`", where "this" is `p_c < p_(2->2)`; and item 2:
  "`||T_(p_(q->q))||_(q->q) = infinity`".
- Textbook facts, used with proofs sketched where short:
  - Russo's formula and the van den Berg–Kesten (BK) inequality for increasing
    events depending on finitely many edges (Grimmett, *Percolation*, 2nd ed.,
    Theorems 2.25 and 2.12);
  - Harris–FKG (ibid., Theorem 2.4);
  - Fekete's lemma for the submultiplicative sequence `|B_n|`.

## Step 0: the invariant set W

For fixed `g, x, y, w` the identities of item 1, the positivity
`Delta_zeta(x,y) in (0,infinity)`, and (when `D < infinity`) the bound
`Delta_zeta(o,s) <= D` for `s in S` each hold off a `nu`-null set. `Gamma` is
countable, so they hold simultaneously on a conull set `E_0`. Put
`W = intersection_(g in Gamma) g E_0`. Each `g E_0` is conull because `nu` is
quasi-invariant, so `W` is conull, and `W` is `Gamma`-invariant. Every
statement below is pointwise on `W`, or on a smaller `Gamma`-invariant conull
set `W'` built the same way.

## Step 1: Schur identity (item 1)

Fix `zeta in W` and `x in Gamma`. By the cocycle identity,
`Delta_zeta(o,y) = Delta_zeta(o,x) Delta_zeta(x,y)`, so

```text
(T_p psi_zeta)(x) = sum_y tau_p(x,y) Delta_zeta(o,y)^(1/2)
                  = psi_zeta(x) sum_y tau_p(x,y) Delta_zeta(x,y)^(1/2).
```

Diagonal invariance with `g = x^(-1)` gives
`Delta_zeta(x,y) = Delta_(x^(-1) zeta)(o, x^(-1) y)`. Left invariance of
percolation gives `tau_p(x,y) = tau_p(o, x^(-1) y)`. Substituting
`y' = x^(-1) y`, the last sum is `X_p(x^(-1) zeta)`. Also `psi_zeta > 0` on
`W`. This proves item 1, as an identity in `[0,infinity]`.

## Step 2: orbit bound (item 2)

**Schur test.** Let `K >= 0` be a symmetric kernel on a countable set, `h > 0`
and `c < infinity` with `sum_y K(x,y) h(y) <= c h(x)` for all `x`. Then for
finitely supported `f, g`, Cauchy–Schwarz with weights gives

```text
sum_(x,y) K(x,y) |f(x)| |g(y)|
  <= ( sum K(x,y) (h(y)/h(x)) f(x)^2 )^(1/2) ( sum K(x,y) (h(x)/h(y)) g(y)^2 )^(1/2)
  <= c ||f||_2 ||g||_2 ,
```

using the hypothesis in `y` for the first factor and, by symmetry, in `x`
for the second. So `||K||_(2->2) <= c`.

Apply this with `K = tau_p` (symmetric), `h = psi_zeta` and
`c = sup_g X_p(g zeta)`. By Step 1,
`(T_p psi_zeta)(x) = psi_zeta(x) X_p(x^(-1) zeta) <= c psi_zeta(x)`. If
`c = infinity` there is nothing to prove. So `||T_p||_(2->2) <= c`.

For the essential-supremum form, let `M = ess sup X_p < infinity`. Rebuild
`W' ⊆ W` from `E_0 ∩ {X_p <= M}`. It is `Gamma`-invariant and conull, hence
nonempty, and for `zeta in W'` the whole orbit has `X_p <= M`.

## Step 3: L2 gradation (item 3)

Expand the square. All terms are nonnegative, so Tonelli applies:

```text
int X_p^2 d nu = sum_(y,y') tau_p(o,y) tau_p(o,y') int (Delta_zeta(o,y) Delta_zeta(o,y'))^(1/2) d nu
              >= sum_y tau_p(o,y)^2 int Delta_zeta(o,y) d nu  =  sum_y tau_p(o,y)^2 .
```

The last equality is the normalisation in item 1.

## Step 4: the ladder (item 4)

- `nu` is a probability, so `L^infinity ⊆ L^2 ⊆ L^1`. This gives
  `p^(nu,infinity)_t <= p^(nu,2)_t <= p^nu_t`.
- By item 2, `X_p in L^infinity` gives `||T_p|| < infinity`, so
  `p^(nu,infinity)_t <= p_(2->2)`.
- `||T_p|| >= ||T_p delta_o||_2 = ||tau_p(o,.)||_2`, so `p_(2->2) <= p_2`.
- Item 3 gives `p^(nu,2)_t <= p_2`.

**The three consequences.**

- *Orbit-bounded at some `p >= p_c`.* `tau_p` increases in `p` entrywise, and
  a nonnegative kernel's `l2` norm is monotone in its entries (take the supremum
  over nonnegative `f, g` in the Schur bilinear form). So
  `||T_(p_c)|| <= ||T_p|| < infinity` by item 2. The sandwich import with
  `N = {e}` gives `p_c < p_(2->2)`, and the Hutchcroft import gives
  `p_c < p_u`.
- *`X_p in L2(nu)` for some `p > p_c`.* Item 3 gives `tau_p(o,.) in l2`.
  - Suppose `p_u < 1` and `t > p_u`. Harris–FKG and uniqueness give
    `tau_t(o,y) >= theta(t)^2 > 0` for all `y`. `Gamma` is infinite, so
    `tau_t(o,.) not in l2`. Hence `p_2 <= p_u`.
  - So `p_c < p <= p_2 <= p_u`.
- *`p >= p_(2->2)`.* Then `||T_p|| = infinity`: above `p_(2->2)` by
  definition and monotonicity, and at `p_(2->2)` by item 2 of the Hutchcroft
  import. By item 2, `sup_g X_p(g zeta) = infinity` for every `zeta in W`.

## Step 5: radial majorants (item 5)

Put `R(zeta) = sum_y f(|y|) psi_zeta(y)`. As in Step 3,
`int R^2 d nu >= sum_y f(|y|)^2 = sum_k f(k)^2 |S_k|`.

Now take `f(k) = gr^(-k/2)`, where `gr = lim |B_n|^(1/n) >= 1`. The sequence
`|B_n|` is submultiplicative, so Fekete gives `gr = inf_n |B_n|^(1/n)`, and
therefore `|B_n| >= gr^n`. Suppose `A = sum_k gr^(-k) |S_k| < infinity`. Then

```text
1 <= gr^(-n) |B_n| = sum_(k <= n) gr^(-k) |S_k| gr^(k-n).
```

Each term tends to `0` as `n -> infinity` (if `gr > 1`) and is dominated by
the summable `gr^(-k) |S_k|`, so the right side tends to `0`, a
contradiction. If `gr = 1`, the series is `sum_k |S_k| = infinity` directly.
So the series diverges.

Consequently, suppose a proof bounds `X_(p_c)` only through a radial majorant
`tau_(p_c)(o,y) <= gr^(-|y|/2)`. This is the form of Hutchcroft's
exponential-growth bound, recalled here and not imported. Then the resulting
majorant `R` is not in `L2(nu)`, whatever `nu` is.

## Step 6: openness of the uniform threshold (item 6)

Assume `D < infinity`, so `Delta_zeta(o,s) <= D` for `s in S` on `W`. Let
`W' ⊆ W` be any `Gamma`-invariant set with `sup_(W') X_(p_0) = M`; `W' = W`
is the case stated. Note `M >= 1`, because `tau_(p_0)(o,o) = psi_zeta(o) = 1`.
Put `C = d D^(1/2)`.

**Truncation.** For `L >= 1` let `A_L(u,v)` be the event that some open path
of length at most `L` joins `u` to `v`. Put `tau^L_q(u,v) = P_q(A_L(u,v))`,
`X^L_q(zeta) = sum_y tau^L_q(o,y) psi_zeta(y)` and
`M^L_q = sup_(zeta in W') X^L_q(zeta)`.

- `A_L(u,v)` is increasing and depends only on finitely many edges. So
  `tau^L_q` is a polynomial in `q`, increasing, and translation invariant.
- The sum defining `X^L_q` runs over `|y| <= L`. The cocycle identity gives
  `psi_zeta(y) <= D^(|y|/2)` on `W`, so `M^L_q <= |B_L| D^(L/2) < infinity`.
- `tau^L_q <= tau_q`, so `M^L_(p_0) <= M`.
- `A_L(o,y)` increases to `{o <-> y}` as `L -> infinity`.

**Russo–BK.** Let `e = {u,v}` be pivotal for `A_L(o,y)`. Then, in the
configuration with `e` open, some self-avoiding open path of length at most `L`
from `o` to `y` uses `e`. Orient `e` in the direction of traversal. The path
splits into two edge-disjoint open paths, each of length at most `L` and
neither using `e`: one from `o` to `u`, one from `v` to `y`. They avoid `e`,
so they are open in the original configuration as well. Hence the pivotal event
is contained in the union over the two orientations of the disjoint occurrence
`A_L(o,u) ∘ A_L(v,y)`. Both events are increasing and depend on finitely many
edges. So Russo and BK give

```text
d/dq tau^L_q(o,y) <= sum_(u in Gamma) sum_(s in S) tau^L_q(o,u) tau^L_q(us,y).
```

Multiply by `psi_zeta(y)` for `zeta in W'`. The cocycle identity gives

```text
psi_zeta(y) = Delta_zeta(o,u)^(1/2) Delta_zeta(u,us)^(1/2) Delta_zeta(us,y)^(1/2).
```

Diagonal invariance gives `Delta_zeta(u,us) = Delta_(u^(-1) zeta)(o,s) <= D`,
since `u^(-1) zeta in W`. As in Step 1,

```text
sum_y tau^L_q(us,y) Delta_zeta(us,y)^(1/2) = X^L_q((us)^(-1) zeta) <= M^L_q .
```

All sums are finite, so they can be differentiated term by term. Summing first
over `y`, then over `u` for each `s`, gives
`d/dq X^L_q(zeta) <= C M^L_q X^L_q(zeta) <= C (M^L_q)^2`.

**Riccati comparison.** Integrate from `p_0` and take the supremum over
`zeta in W'`:

```text
M^L_q <= u(q) := M + C int_(p_0)^q (M^L_r)^2 dr ,   q >= p_0 .
```

The integrand is bounded, and measurable because `M^L_r` is monotone in `r`.
So `u` is absolutely continuous, `u >= 1`, and `u' = C (M^L_q)^2 <= C u^2`
almost everywhere. Hence `(1/u)' >= -C` a.e., so `1/u(q) >= 1/M - C (q - p_0)`.
For `0 <= q - p_0 < 1/(C M)`,

```text
X^L_q(zeta) <= M^L_q <= M / (1 - C M (q - p_0))     (zeta in W').
```

The bound does not depend on `L`. Monotone convergence as `L -> infinity`
gives the same bound for `X_q(zeta)` on `W'`, which proves item 6. With `W'`
built from `E_0 ∩ {X_(p_0) <= ess sup X_(p_0)}`, the same holds with `ess sup`
on both sides.

## Remark: what the theorem does not say

- There is no converse to item 2: `||T_p|| < infinity` need not make `X_p`
  bounded. Item 4 of `fpbs-boundary-tilted-susceptibility-kernel` gives
  `p_(2->2) <= p^nu_t` only under `pi_nu ≺ lambda`, and only in `L1(nu)`.
- Nothing is said about `L^r(nu)` for `1 < r < 2`.
