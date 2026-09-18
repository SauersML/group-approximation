---
rg: 2
id: dense-link-square-selectors-reduce-to-base-orientations
kind: claim
title: On the 2-to-2 square of a 2-to-1 game along an alpha-dense link coupling, a deterministic pivot turns any matching selection of unique-game value 1 - xi into an orientation of the base game with lift value 1 - 13 xi / alpha^3, so 2-to-2 selectors on dense-link squares of rigid doubled LECs, including the DKKMS derived 2-to-2 game, put the source in RP
distinct_from:
  near-perfect-selectors-die-on-every-rigid-doubled-lec: that kills orientations of the 2-to-1 game itself and lists 2-to-2 inner games as not covered; this reduces matching selections on the 2-to-2 square to orientations of the 2-to-1 base with an explicit loss, so that kill extends to the square.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the OPEN selector hole; this closes its 2-to-2 inner-game survivor on dense-link squares, under NP not in RP, and names the invariant that the rest of the 2-to-2 survivor must break.
  orientation-lifts-sandwich-2to1-game-values: that bounds the value of an orientation lift by the value of its 2-to-1 game; this compares two kinds of selectors, matchings on the square and orientations on the base, and shows each simulates the other with a constant-factor loss.
  efficient-branch-selectors-list-decode-honest-outer-labels: that decodes outer labels from a good orientation; this produces the good orientation from a good 2-to-2 matching selection and does no decoding.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that computes the value of the branch-blind affine-view coarsening of the DKKMS 2-to-1 and derived 2-to-2 games; this is about arbitrary polynomial-time matching selections on the derived 2-to-2 game, and shows they are no stronger than orientations of the 2-to-1 game.
artifacts:
  - experiments/ugc-square-transfer-2026-09-17/check_square_transfer.py
---

**ESTABLISHED.** Route: `dense-link-square-selectors-reduce-to-base-orientations-proof`.

## Setting (dense-link square)

`G` is a 2-to-1 game with left vertices `P`, right vertices `Q ~ nu`, and on
each constraint `e = (p_e, q_e)` an exactly 2-to-1 onto map
`pi_e : Sigma_(p_e) -> Sigma_(q_e)`. The star `star(q)` carries the law `mu_q`
(the `mu`-law of `e` given `q_e = q`). Each `e` lies in exactly one star.

A **link coupling** `J = (J_q)` gives each `q` a symmetric probability measure
`J_q` on `star(q) x star(q)` whose marginals are both `mu_q`. It is
**alpha-dense** if

```text
J_q(e1, e2)  >=  alpha mu_q(e1) mu_q(e2)     for all e1 != e2 in star(q).
```

Replacing `alpha` by `min(alpha, 1)` keeps this true, so assume `0 < alpha <= 1`.

The **square** `H = Sq_J(G)` is the 2-to-2 game on the left vertices `P`. It
draws `q ~ nu` and `(e1, e2) ~ J_q`, and it accepts `(sigma1, sigma2)` at
`(p_(e1), p_(e2))` iff `pi_(e1)(sigma1) = pi_(e2)(sigma2)`. The constraint is a
union of `K_(2,2)` blocks, one per `tau in Sigma_q`.

**Reference bits.** `r_e(sigma) in {0,1}` is 0 on the smaller element of the
fibre `pi_e^(-1)(pi_e(sigma))` and 1 on the larger one. Any fixed rule works.

**Selections.** A *matching selection* `kappa` chooses one perfect matching in
every block. Equivalently it chooses a bit `kappa^tau(e1, e2)` for each pair in
the support of `J_q` and each block `tau`. The matching sends `sigma1` in the
block to the `sigma2` with `r_(e2)(sigma2) = r_(e1)(sigma1) xor kappa^tau(e1, e2)`.
The unique game `U_kappa` keeps the law of `H` and replaces each block by its
chosen matching. It accepts iff `pi_(e1)(sigma1) = pi_(e2)(sigma2) = tau` and
`r_(e2)(sigma2) = r_(e1)(sigma1) xor kappa^tau(e1, e2)`. This is the most
general way to turn `H` into a unique game constraint by constraint. A 2-to-2
*selector* is a polynomial-time algorithm that computes `kappa`.

An *orientation* `o` of `G` and its doubled lift `U_o` are as in
`orientation-lifts-sandwich-2to1-game-values`. The lift has right alphabet
`Sigma_q x {0,1}` and the bijection `sigma -> (pi_e(sigma), o_e(sigma))`.

## Pivot orientation

Given `kappa`, put `kbar^tau(e1, e2) = kappa^tau(e1, e2)` for `e1 != e2` and
`kbar^tau(e, e) = 0`. For each `q`, each `tau in Sigma_q` and each pivot
`e* in star(q)`, let

```text
g^tau_(e*)(e) = kbar^tau(e*, e),        e in star(q),
V(e*)         = J_q{ (e1, e2) : g^tau_(e*)(e1) xor g^tau_(e*)(e2) = kbar^tau(e1, e2) }.
```

Let `g_(q, tau)` be `g^tau_(e*)` for the first `e*` that maximises `V`. Since
`alpha > 0`, every off-diagonal pair of `star(q)` lies in the support of `J_q`,
so `kbar^tau(e*, e)` is always defined. Put

```text
o_e(sigma) = r_e(sigma) xor g_(q_e, pi_e(sigma))(e).
```

This is an orientation, because `r_e` separates each fibre and `g` is constant
on it. It is deterministic and runs in time `O(sum_q |Sigma_q| |star(q)|^3)`.

## Statement

**Theorem Q (square transfer).** Let `J` be alpha-dense, `kappa` any matching
selection, and `o` its pivot orientation. For every left labelling `A` of `P`,
there are right labels `B` such that

```text
val_(U_o)(A, B)  >=  1 - 13 xi / alpha^3,        xi := 1 - val_(U_kappa)(A).
```

In particular `opt(U_o) >= 1 - 13 (1 - opt(U_kappa)) / alpha^3`.

**Theorem Q' (converse).** Every orientation `o` of `G` induces a selection
`kappa(o)`: in each block, match the two elements with equal `o`-bit. Then
`opt(U_(kappa(o))) >= 1 - 2 (1 - opt(U_o))`.

So on dense-link squares, 2-to-2 matching selectors and 2-to-1 orientation
selectors reach near-perfect completeness together. Each one converts into the
other in polynomial time, and the loss is linear in `xi`.

**Corollary Q1 (kill on rigid doubled LECs).** Let `x -> D(x)` be a doubled LEC
satisfying (E), (M=), (Rig(xi, zeta, eps, d)) and (S) of
`near-perfect-selectors-die-on-every-rigid-doubled-lec`. Let `x -> J(x)` be a
polynomial-time alpha-dense link coupling on its 2-to-1 game `G(x)`, with
`alpha` a constant. Suppose a randomized polynomial-time 2-to-2 selector on
`Sq_(J(x))(G(x))` satisfies, for every YES input,

```text
Pr[ opt(U_kappa) >= 1 - alpha^3 xi / 13 ]  >=  theta(|x|)  >=  1/poly(|x|).
```

Then `Lang in RP`.

**Corollary Q2 (DKKMS derived 2-to-2).** The derived 2-to-2 game of the folded
DKKMS instances, in which two members sharing a B-vertex must agree on `L'`, is
`Sq_J(G_folded)` when it is taken with its natural law: draw a B-vertex, then
two independent constraints at it. That is the product coupling
`J_q = mu_q x mu_q`, so `alpha = 1`. At every DKKMS-certified parameter point
with soundness below `1/16`, a polynomial-time 2-to-2 selector with YES value
at least `1 - 10^(-5)/13` (with inverse-polynomial probability) puts NP in RP.
The same holds with `10^(-5) alpha^3 / 13` for any other law of two constraints
at a common B-vertex, provided it has marginals `mu_q` and dominates
`alpha mu_q x mu_q` off the diagonal.

The artifact checks Theorems Q and Q' by brute force: 3000 random instances
(product, distinct-pair and mixed couplings, star sizes 2 to 5), every left
labelling, and noisy planted selections. All 241467 checks pass. The worst
observed ratio `alpha^3 (1 - val_o) / xi` at `xi < 0.1` is `1.33`, and the
bound is 13.

## What it does to the hole (impact types 2 and 3)

The "Not covered" list of `near-perfect-selectors-die-on-every-rigid-doubled-lec`
names "2-to-2 inner games" as a survivor of
`parity-leaking-branch-selectors-reach-near-perfect-completeness` (H1). That
survivor splits as follows.

**Killed (under NP not in RP).** Every 2-to-2 inner game that is a dense-link
square `Sq_J(G)` of a doubled LEC satisfying (E), (M=), (Rig) and (S), with
`alpha` bounded below by a constant. The invariant is the pivot identity: on a
dense link, a matching selection of value `1 - xi` agrees with the pivot
difference cocycle `kbar(e*, e1) xor kbar(e*, e2)` outside `O(xi/alpha^2)`. So
the selection is, up to that error, an orientation of the base, and every
member dies at the step where Theorem S\* is applied to that orientation.
This includes the DKKMS derived 2-to-2 game at every certified point
(Corollary Q2).

**Why this is not the end of 2-to-2.** Every 2-to-2 game `H` is a square with
`alpha = 1` of its edge subdivision `Sub(H)`. Give each constraint `(u, v)` of `H`
its own right vertex `q_uv`, whose alphabet is the set of blocks, and give it
the two 2-to-1 edges `(u, q_uv)` and `(v, q_uv)`. Take `J_q` uniform on the two
ordered off-diagonal pairs. Then `mu_q` is uniform on the two edges and
`J_q = 2 mu_q x mu_q` off the diagonal. But every star of `Sub(H)` has size 2,
so given `q_e` the direction `x_e` takes at most two values. Hypothesis (E)
then fails badly for `m >= 2`, and Theorem S\* does not apply. So the transfer by itself proves
nothing about general 2-to-2 games. The operative invariant is the following:

> *the 2-to-2 game has a dense-link square presentation whose 2-to-1 base
> satisfies (E), (M=), (Rig) and (S).*

What survives of the 2-to-2 cell of H1 is exactly the families without such a
presentation:

* (T1) **sparse links.** The coupling at a B-vertex is supported on
  `o(|star|^2)` pairs, so `alpha -> 0`. The loss `13/alpha^3` then blows up.
  This covers the constraint-removing modification of KMS TR16-124 Remark 1.11
  (`kms-2to2-reduction-is-sound-only-for-colorings`) whenever the removal is
  not uniform on links.
* (T2) **thin presentations only.** Every dense-link square presentation has
  stars too small, or directions too concentrated, for (E), as with `Sub(H)`.
* (T3) a dense-link base that fails one of (F1) to (F4) of
  `near-perfect-selectors-die-on-every-rigid-doubled-lec`.

The constant-bias cell of H1 is untouched, because it concerns completeness
bounded away from 1.
