---
rg: 2
id: fpbs-t4xz-certified-critical-l2-gap-proof
kind: route
title: A closed-form fibre-interval Galton-Watson bound and an exact 4-cycle-avoiding Busemann Schur test certify the critical l2 gap on T_4 x Z
target: fpbs-t4xz-certified-critical-l2-gap
requires: []
artifacts:
  - experiments/fpbs-t4xz-certificate-2026-09-17/rho2v.py
  - experiments/fpbs-t4xz-certificate-2026-09-17/certschur.py
  - experiments/fpbs-t4xz-certificate-2026-09-17/certify_all.py
  - experiments/fpbs-t4xz-certificate-2026-09-17/outputs.txt
---

**Setting.**
* `X_k = Cay(F_k x Z, S)` with `S = {a_1^(±1), ..., a_k^(±1), t^(±1)}`, `k >= 2`.
  Vertices are `(w,h)`, `w in F_k`, `h in Z`.
* Edges: *vertical* `(w,h) ~ (w,h+1)` and *ladder* `(w,h) ~ (w a_i^(±1), h)`.
  The graph is `(2k+2)`-regular and transitive, and it is the Cartesian
  product `T_{2k} □ Z`.
* `tau_p(x,y) = P_p(x <-> y)`, `theta(p) = P_p(|C(o)| = infinity)`, `T_p` is
  the operator with kernel `tau_p`, and
  `p_{2->2} = sup{p : ||T_p||_{2->2} < infinity}`.

The proof has three steps:
1. `theta(p1) > 0` and `||T_(p2)|| < infinity` with `p1 < p2` give
   `p_c <= p1 < p2 <= p_{2->2}` and `p2 <= p_u`.
2. `theta(p) > 0` whenever `m_k(p) > 1`.
3. `||T_p|| < infinity` for `p < 200/829` when `k = 2`, and for
   `p < 1/(2+2 sqrt(2k-1))` for every `k`.

Then the checks in `certify_all.py` finish the proof.

## Step 1. From the two bounds to strict thresholds

This is Step 1 of `fpbs-rigid-f2xz-certified-strict-thresholds-proof`, which
uses nothing about the generating set. Suppose `theta(p2) > 0` and there is
a.s. a unique infinite cluster at `p2`.
* By Harris-FKG and uniqueness,
  `tau_(p2)(o,x) >= P(o <-> infinity, x <-> infinity) >= theta(p2)^2` for
  every `x`.
* So `sum_x tau_(p2)(o,x)^2 = infinity`, contradicting
  `sum_x tau(o,x)^2 = ||T δ_o||^2 <= ||T||^2`.

So `p2` is in the nonuniqueness phase. Uniqueness is monotone in `p`
(Häggström-Peres 1999; Schonmann 1999), hence `p2 <= p_u`. Also
`p_c <= p1 < p2 <= p_{2->2}` by definition.
Here `theta(p2) >= theta(p1) > 0` by monotonicity.

## Step 2. The fibre-interval Galton-Watson process

**Individuals.** An individual is a pair `(w, h)` with `w != e`, where `w` is a
fibre and `(w,h)` is known to lie in `C(o)`. Write `w = w' s` in reduced form,
so `s` is the last letter of `w` and `w'` is the parent fibre. The *child
letters* of `w` are the `2k-1` letters `l != s^(-1)`, and the children fibres
are `w l`. The root individual is `(e, 0)`, with all `2k` letters as child
letters.

**Stage of `(w,h)`.** It reveals edges in this order.
1. The vertical edges `(w,h+i) ~ (w,h+i+1)` for `i = 0, 1, ...` up to and
   including the first closed one. Then `(w,h-i) ~ (w,h-i-1)` in the same way.
   The open ones give an interval `I = [h-X, h+Y]` of `L = 1+X+Y` vertices, all
   in `C(o)`.
2. For each child letter `l`, the ladder edges `(w,g) ~ (wl,g)` for
   `g in I` in increasing order, up to and including the first open one. If an
   open one is found at `g`, then `(wl, g)` is in `C(o)` and becomes a child
   individual.

**Why this is a Galton-Watson process.**
* *Stages own disjoint edge sets.* The stage of `w` reveals only vertical edges
  of fibre `w` and ladder edges between `w` and its children `wl`. The fibres
  that become individuals form a subtree of the Cayley tree of `F_k` rooted at
  `e`. Each fibre is an individual at most once, because it has one parent.
  So each vertical edge belongs to at most one stage, and so does each ladder
  edge `{w, wl}`: it belongs to the parent end of the tree edge.
* *The stage outcome is a function of its own edges only*, and the order of
  revealing is fixed in advance, given the type.
* *The offspring law does not depend on `(w,h)` for `w != e`.* Left
  multiplication by `F_k` and translation in `Z` are automorphisms of `X_k`.
  They carry the stage of `(w,h)` to the stage of `(a_1, 0)` (up to a relabelling
  of the letters).

So the individuals other than the root form a single-type Galton-Watson
process. It has at most `2k-1` children per individual, and its mean is `m_k(p)`,
computed below. The root has at most `2k` children and has at least one child
with positive probability. Every individual lies in `C(o)`, and distinct
individuals are distinct vertices. So survival forces `|C(o)| = infinity`.

**The mean.**
* `X` and `Y` are independent with `P(X >= j) = p^j`, since each vertical
  edge is revealed once and is open with probability `p`.
* Given `L`, the child letters behave independently: letter `l` has a child
  with probability `1 - (1-p)^L`, because its `L` ladder edges are distinct and
  unrevealed.
* So `m_k(p) = (2k-1)(1 - E (1-p)^L)`.
* `E s^X = sum_(j>=0) (1-p) p^j s^j = (1-p)/(1-ps)`. At `s = 1-p` this is
  `phi = (1-p)/(1-p+p^2)`.
* Hence `E (1-p)^L = (1-p) phi^2` and `m_k(p) = (2k-1)(1 - (1-p) phi^2)`.

**Conclusion.** If `m_k(p) > 1`, the process survives with positive
probability (a Galton-Watson process with bounded offspring and mean `> 1`).
Hence `theta(p) > 0` and `p_c(X_k) <= p`.

## Step 3. Bounds on `||T_p||`

**Adjacency bound, every `k`.** Every self-avoiding path is a walk, so
`tau_p <= sum_n p^n A^n` entrywise. The right side is a nonnegative symmetric
kernel of norm at most `sum_n (p ||A||)^n`. A nonnegative symmetric kernel
dominated entrywise by another has no larger `l^2` norm (pointwise `|T f| <= S |f|`, so
`||T f|| <= ||S|| ||f||`). So `||T_p|| < infinity` when `p ||A|| < 1`. Here
`||A|| = ||A_(T_{2k})|| + ||A_Z|| = 2 sqrt(2k-1) + 2`, since the adjacency
operator of a Cartesian product is `A_1 ⊗ 1 + 1 ⊗ A_2` with commuting summands.

**Busemann Schur bound, `k = 2`.** This is Step 3 of
`fpbs-rigid-f2xz-certified-strict-thresholds-proof`, run with the ladder
offsets `D_a = D_b = {0}` in place of `{0,1,3}` and `{0,1,4}`, and with
`ell = 4`. The argument uses nothing else about the generating set. In brief:
* `W_n(x,y)` counts walks with `x_t != x_(t-j)` for `2 <= j <= 4`. Every
  self-avoiding path is such a walk, so `tau_p <= S_p <= M_p := sum_n p^n W_n`,
  where `S_p = sum_n p^n SAW_n` is symmetric.
* Fix an end `xi` of `T_4` with Busemann function `beta`, and put
  `h(w,z) = u^(-beta(w))` with `u = 1732/1000`. The step factors are `1`
  (vertical), `u` (the letter toward `xi`) and `1/u` (the other three letters).
* A state is the last three steps, with no cycle of length `<= 3` among their
  partial products. There are 150 states (`6 * 5 * 5`, since `X_2` has no
  triangles). A transition appends a step whose suffixes of length 2, 3, 4
  are not the identity. The transfer map `F` on `c : states x letters -> (0,infinity)`
  is as in the rigid proof.
* If `F(c) <= lambda c`, then by induction on the length the weighted sum of
  continuations of length `n` is at most `lambda^n max c / min c`. The first
  three steps contribute at most `(6u)^3`. So `sum_y M_p(x,y) h(y) <= C h(x)`
  when `p lambda < 1`, and the Schur test gives `||T_p|| <= ||S_p|| <= C`.
* `certschur.py` rounds the float Perron vector up to integers
  `ci = ceil(10^9 c) + 1`. It checks `200 * UN*UD*F(ci) <= 829 * UN*UD * ci`
  entrywise in exact integers, with `u = UN/UD`. Each entry is a sum of at most
  6 terms, each below `4 * 10^15`, so there is no overflow. The output is
  `exact max ratio 4.14465169467... <= lam 829/200 : True`.

So `||T_p|| < infinity` for `p < 200/829 = 0.241254...`.

**Calibration of the program on `X_2`.**
* `ell = 1` returns `2 + 2 sqrt 3 = ||A||`.
* `ell = 2` returns `4.30180`, the root of `lambda + 5/lambda = 2 + 2 sqrt 3`,
  as the Ihara formula predicts for non-backtracking walks.
* `ell = 3` returns the same value, since `X_2` has no 3-cycles.

## Step 4. The exact checks (`certify_all.py`)

All arithmetic is in `Fraction`, and `sqrt(2k-1)` enters only through the
exact test `((1/p - 2)/2)^2 > 2k-1`.

| `k` | `p1` | `m_k(p1)` | `p2` | check on `p2` |
|---|---|---|---|---|
| 2 | `236/1000` | `1.00888...` | `241/1000` | `p2 * 829/200 = 0.998945 < 1` |
| 3 | `1544/10000` | `1.00067...` | `1545/10000` | `p2 (2 + 2 sqrt 5) < 1` |
| 4 | `12/100` | `1.03675...` | `13/100` | `p2 (2 + 2 sqrt 7) < 1` |

For `k >= 5`, `phi <= 1` gives `m_k(p) >= (2k-1) p`, so `p_c <= 1/(2k-1)`.
And `1/(2k-1) < 1/(2 + 2 sqrt(2k-1))` iff `sqrt(2k-1) > 1 + sqrt 3`, i.e.
`2k-1 > 4 + 2 sqrt 3 = 7.46...`, which holds for `k >= 5`. So any `p1 < p2`
strictly between the two works. The script also checks `k = 5..59` in
rationals. This case is already `fpbs-expanding-factor-product-strict-thresholds`.

With Steps 1–3 this proves `p_c(X_k) <= p1 < p2 <= p_{2->2}(X_k) <= p_u(X_k)`
for every `k >= 2`.

## Reproduction

```text
cd experiments/fpbs-t4xz-certificate-2026-09-17
python3 certschur.py 4 1732/1000 400 1732/1000 4145/1000   # "... <= lam 829/200 : True"
python3 certify_all.py                                       # "ALL OK"
gcc -O2 -o mc mc.c && ./mc 0.22 2000 100000 2                # calibration only
```

`rho2v.py` writes `rho2_c_ell*.npy` in the working directory, and these files
are not needed. Recorded outputs are in `outputs.txt`. Verification tier: an
exact integer certificate from a program in the artifact directory, a
closed-form one-type Galton-Watson computation, and standard theorems. The
Schur program is the program of the rigid certificate with the offsets
changed. Nobody has independently re-implemented it.
