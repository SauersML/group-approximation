---
rg: 2
id: view-local-branch-selectors-are-gauge-blind
kind: claim
title: On gauge-randomised Grassmann 2-to-1 instances, every branch selector whose per-edge view sees no parity of window variables beyond the window's own equations has honest orientation-lift value at most one half plus its parity leakage, uniformly over any equivariant witness menu of subexponential size
invalidates:
  - rich-2to1-via-view-local-branch-selectors
distinct_from:
  unique-constraints-orient-at-most-half-of-a-fiber: that is the combinatorial fact that a network of bijections keeps one preimage per fiber; this is an information bound on which preimage a computed orientation can pick, and it applies to arbitrary (even non-uniform, non-efficient) selectors, gated only by what they read.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that shows the branch-blind coarsening has a gauge labelling F* of value 1 on every instance; this concerns the complementary branch coordinate x_e, shows it is exactly uniform under the gauge group once the view is parity-faithful, and bounds completeness rather than soundness.
  perfect-completeness-rich-2to1-tractable-skeletons-are-in-p: that turns a computable skeleton into a polynomial-time algorithm at completeness 1; this uses no algorithm and no perfect completeness, only the symmetry z -> I^z of the 3LIN source.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that is about views of the outer label inside a verifier; here the view is the part of the input instance (right-hand sides) the selector reads.
artifacts:
  - experiments/ugc-heretic-2026-09-17/check_gauge_blind_selectors.py
---

**ESTABLISHED.** Route: `view-local-branch-selectors-gauge-blindness-proof`.
The proof is self-contained linear algebra plus McDiarmid's inequality, and it
is summarised below. The artifact checks the exact part exhaustively.

## Setting

A 3LIN instance is `I = (M, b)`: rows `m_j in F_2^n` of weight 3 and right-hand
sides `b_j`. For `z in F_2^n` the **gauge** `I^z = (M, b + Mz)`. Then
`A |-> A + z` maps the assignments of `I` bijectively to those of `I^z` and
satisfies exactly the same equations. So `z -> I^z` is a polynomial-time map
that preserves the value exactly, and composing any hardness reduction from 3LIN
with a random or arbitrary gauge is again a hardness reduction.

A **Grassmann 2-to-1 instance over `I`** is any weighted 2-to-1 game `D(I)` of the
DKKMS shape (see `grassmann-composed-2to2-coarsenings-are-satisfiable`, the
verbatim DKKMS import, and `two-to-two-games-theorem`). It has the following
structure:
- vertices, subspaces and weights depend on `M` only;
- an edge `e` joins an A-vertex `(U, L)` to a B-vertex with subspace `L' < L` of
  codimension 1, where `U` is a tuple of `k` equations, `X_U` is the span of
  their variables, `H_U = Span(m_j : j in U)`, and `L <= X_U` with
  `L meet H_U = 0`;
- `b` enters only through the folding offsets `h_U`.

The folded DKKMS instances are of this form. Fix a branch vector
`x_e in L \ L'`.

An **orientation** chooses, for each edge `e`, a map `o_e : (L')^* -> F_2`. The
orientation lift `U_o` accepts `(sigma, tau)` iff `sigma|L' = tau` and
`sigma(x_e) = o_e(tau)`, where `sigma` is the unfolded A-label. A **selector** `S`
is any map `I -> o`. It is **view-local with views `J_e`** if `o_e` depends on the
instance only through `M` and `(b_j)_(j in J_e)`, where `J_e` depends only on `M`
and `e`. Put
```text
Q_e := Span(m_j : j in J_e) + H_(U_e).
```
- Condition **(F)** at `e` (the view is parity-faithful): `Q_e meet X_(U_e) = H_(U_e)`.
- **Parity leakage** `w_bad(S)`: the weight of edges where (F) fails.

For an assignment `t`, the **honest labelling** gives each A-vertex `(U, L)`
whose equations `t` satisfies the label `t|L`, and gives each B-vertex the label
`t|L'`. The **honest lift value** `hon_t(o)` is the weight of the edges `e` for
which `U_e` is satisfied by `t` and `o_e(t|L'_e) = t(x_e)`.

## Theorem 1 (exact gauge blindness)

Fix `M`, `b`, a view-local selector `S` and an assignment `t`. Let `z` be uniform
in `F_2^n`, and let `o^z = S(I^z)`.

1. For every edge `e` satisfying (F), for every value of the view
   `(b_j + <m_j,z>)_(j in J_e)`, and for every `tau`, the bit `(t+z)(x_e)` is
   uniform and independent of that view and of `(t+z)|L'_e`. Hence
   `Pr_z[ o^z_e((t+z)|L'_e) = (t+z)(x_e) ] = 1/2`, and this is exact for every
   selector with that view, whether or not it is efficient or uniform.
2. `E_z hon_(t+z)(o^z) <= 1/2 + w_bad(S)/2`.

*Proof.* The view, the B-label and the branch bit are affine functions of `z`,
with linear parts `z -> (<m_j,z>)_(j in J_e)`, `z -> (<y,z>)_(y in L')` and
`z -> <x_e, z>`. A uniform `z` makes `<x_e,z>` uniform and independent of the
other two whenever `x_e notin L' + Span(m_j : j in J_e)`. It is enough to show
`x_e notin L' + Q_e`. Suppose `x_e = y + q` with `y in L'` and `q in Q_e`. Then
`q = x_e + y in X_U meet Q_e = H_U` by (F), so `x_e + y in L meet H_U = 0`. That
gives `x_e = y in L'`, a contradiction. The satisfaction of `U_e` by `t+z` in
`I^z` does not depend on `z`. So each (F)-edge contributes exactly half its
weight whenever `U_e` is satisfied, and each other edge contributes at most its
weight. QED.

## Theorem 2 (witness menus)

Let `S_e` be the set of variables of `U_e` together with those of the equations
in `J_e`. Put `s := max_e |S_e|` and `d_max := max_i w{e : i in S_e}`. Let
`T = T(I)` be any finite set of assignments that is **equivariant**, meaning
`T(I^z) = T(I) + z`. Examples are all assignments of value at least `1 - eps`,
or a singleton planted witness transported by the gauge. Then for every `gamma > 0`,
```text
Pr_z[ max_(t' in T(I^z)) hon_(t')(S(I^z)) >= 1/2 + w_bad/2 + gamma ]
    <= |T(I)| * exp( -2 gamma^2 / (d_max * s) ).
```
*Proof.* Write `f_t(z) = hon_(t+z)(S(I^z))`. The term for edge `e` depends on `z`
only through the coordinates in `S_e`. So flipping `z_i` changes `f_t` by at most
`d_i := w{e : i in S_e}`. McDiarmid's inequality gives
`Pr[f_t >= E f_t + gamma] <= exp(-2 gamma^2 / sum_i d_i^2)`, and
`sum_i d_i^2 <= d_max * sum_i d_i <= d_max * s`. Theorem 1 gives
`E f_t <= 1/2 + w_bad/2`. A union bound over `t in T(I)` finishes the proof. QED.

The same bound holds with `d_max` replacing the Lipschitz constant in `t`. So a
menu covered by `N` Hamming balls of radius `rho n` obeys the same bound with
`|T|` replaced by `N` and `gamma` by `gamma + rho n d_max`. On a `D`-regular
source with uniformly sampled `k`-tuples and bounded-radius views, `s = O(1)` and
`d_max = O(s/n)`. The bound then kills menus of size `exp(c gamma^2 n / s^2)`.

## Class kill

Consider any proof of completeness above one half for an orientation lift of
Grassmann 2-to-1 instances that runs through three steps:
- (i) a selector that is view-local with leakage `w_bad <= eta_1`;
- (ii) a guarantee that on every YES input some honest labelling from an
  equivariant menu of size `exp(o(1/(d_max s)))` has lift value `c`;
- (iii) the gauged source `I^z`, which is itself a YES input.

Every such proof needs `c <= 1/2 + eta_1/2 + o(1)`, and it dies at step (ii) on
most gauges. The invariant is the visible parity space `Q_e meet X_(U_e)`. The
step where every member dies is the conditional uniformity of the branch bit
`(t+z)(x_e)` given the view and the B-label. So a selector reaching completeness
`1 - eta'` must satisfy `w_bad >= 1 - 2 eta' - o(1)`. On almost every edge its
view must contain equations that close a parity cycle through the window's
variables.

The artifact measures radius-1 views on random 3LIN with `m = 2n` and `k = 3`.
(F) fails on 9 of 200 windows at `n = 300` and on 0 of 200 at `n = 3000`. Bounded
views on sparse high-girth sources are therefore parity-faithful. The obstruction
is about views, not about efficiency: global views (`Q_e = F_2^n`) are untouched.

**Survivors.**
- (a) parity-leaking or global selectors;
- (b) certificates through unclustered menus of size `exp(Omega(n / s^2))`;
- (c) certificates through non-honest lift labellings, for example
  zoom-structured ones.

The node for (a) is `parity-leaking-branch-selectors-reach-near-perfect-completeness`.
The node for (b) and (c) is
`view-local-selectors-beat-one-half-through-non-honest-witnesses`.

## Check

`python3 experiments/ugc-heretic-2026-09-17/check_gauge_blind_selectors.py`,
default seed 20260918, 120 trials per configuration. It covers four window
configurations (`k in {1,2}`, `l in {2,3}`) with extra variables and visible
equations, 480 windows in total.

For each window it enumerates all `z in F_2^n` (`n <= 12`) and tabulates the
branch bit per (view, B-label) cell. This gives the best agreement over all
selectors at once. The results:
- 0 violations of "(F) implies `x_e notin L' + Q_e`";
- 0 unbalanced cells when `x_e notin L' + Q_e` (331 windows);
- in every leaking window (149), some selector reaches agreement 1, which is
  the control.

This neither proves nor refutes UGC or the Rich 2-to-1 Conjecture.
