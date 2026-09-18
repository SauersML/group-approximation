---
rg: 2
id: fpbs-planar-stretch-bounded-below-by-dual-piece-mass
kind: claim
title: On surface-group tilings the linear chemical stretch constant just above p_u is at least the dual Cheeger constant times the critical two-sided dual piece mass
distinct_from:
  fpbs-uniform-chemical-stretch-above-pu: that asserts sup over t>p_u of K_* is finite on every nonamenable Cayley graph; this proves a lower bound for K_* on planar surface-group graphs, so that (UCS) there forces a finite critical dual half-plane piece mass
  fpbs-intrinsic-l2-rate-closed-zero-set: item 6 there forces K_* to blow up at p_c+ through lambda_1; this forces a lower bound at p_u+ through planar duality, where lambda_1 is positive
---

**ESTABLISHED.** Proof in `fpbs-planar-stretch-bounded-below-by-dual-piece-mass-proof`.

**Setting.**

- `Gamma_g` (`g >= 2`) is the genus-`g` surface group with standard generators
  `S`. `G = Cay(Gamma_g,S)` is the `{4g,4g}` tiling of the hyperbolic plane,
  and `G†` is its dual, also a `{4g,4g}` tiling.
- `h = sqrt((4g-2)^2 - 4)` is the edge isoperimetric constant of `G†`.
- `a in S` is a standard generator. `L` is the bi-infinite edge path
  `(a^k)_(k in Z)` with edges `e_k = {a^k, a^(k+1)}`. It is a properly embedded
  line, so it splits the plane into two sides `H_+` and `H_-`.
- `omega_t` is Bernoulli(`t`) bond percolation. `f_+(e)` and `f_-(e)` are the
  two faces adjacent to an edge `e` of `L`, one on each side.

**Pieces.** Form the graph on faces whose edges are the dual edges `e†` with
`e` closed and `e` not on `L`. Its components never cross `L`. For a closed edge
`e = e_k` define:

- `P_+(e)` and `P_-(e)`: the components of `f_+(e)` and `f_-(e)` in this graph;
- `m_+(e)`: the number of closed edges `e'` of `L` with `P_+(e') = P_+(e)`, and
  `m_-(e)` likewise;
- the **two-sided piece weight**
  `y(e) = min( |P_+(e)|/m_+(e), |P_-(e)|/m_-(e) )`, with `y(e) = 0` if `e` is
  open.

These are finite for `t >= p_u` by `fpbs-hyperbolic-tiling-dual-clusters-bounded-from-pu`.
Write `mu(t) = E_t[ y(e_0) ]`, a value in `[0, infinity]`.

**Theorem.**

1. *(Deterministic area bound.)* For every `n >= 1` and every configuration
   in which the pieces of all closed `e_k`, `0 <= k < n`, are finite,
   `d_omega(o, a^n) >= h * sum_(k=0)^(n-1) y(e_k) - n`.
2. *(Stretch bound at a fixed parameter.)* For every `t in [p_u, 1)`,
   `K_*(t) >= h mu(t) - 1`. If `mu(t) = infinity`, no linear stretch constant
   exists at `t`.
3. *(At `p_u+`.)* `sup_(t > p_u) K_*(t) = lim_(t↓p_u) K_*(t) >= h mu(p_u) - 1`.
   In particular, (UCS) on `G` implies `mu(p_u) < infinity`, and
   `mu(p_u) = infinity` refutes (UCS).

**Reading.** `mu(p_u)` concerns critical dual percolation (`p_c(G†) = 1-p_u`)
cut along one line.

- `P_+` and `P_-` use disjoint edge sets, so they are independent.
- `y` is at most the size of the critical dual cluster, and that cluster has
  infinite mean. The infinite mean is the standard divergence of the
  susceptibility at `p_c`; it is recalled here, not used in the proof.
- Whether `mu(p_u)` is finite is recorded as the OPEN
  `fpbs-planar-critical-two-sided-dual-piece-mass-infinite`.
