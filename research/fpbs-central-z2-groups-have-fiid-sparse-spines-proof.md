---
rg: 2
id: fpbs-central-z2-groups-have-fiid-sparse-spines-proof
kind: route
title: Thin Bernoulli crosses inside each Z2-coset, renormalize to supercritical site percolation, and link neighbouring cosets along whole central lines
target: fpbs-central-z2-groups-have-fiid-sparse-spines
requires:
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
---

Notation is as in the target. `Gamma` acts on itself, on `E(G)` and on left
cosets by left multiplication. Words are read by right multiplication, so they
commute with this action. For a vertex `x` and an `S`-word `w = s_1...s_l`,
`P(x,w)` is the path `x, x s_1, ..., x s_1...s_l`, and `gP(x,w) = P(gx,w)`.
`MTP` is the mass-transport principle on the unimodular graph `G`.

## Lemma 0 (no finite invariant sets; see `fpbs-soft-collapse-iff-invariant-sparse-spines-proof`)

For a countable group `A` acting freely and transitively on a set `X`, and a
random subset `Y ⊆ X` with `A`-invariant law, `P(0<|Y|<infinity)=0`. The proof
is the mass transport `1/|Y|` from every point to every point of `Y`. We use
it for `A = <t> ≅ Z` acting on a line `v<t>`.

## Setup

Fix `t` central of infinite order and `g` with `<g> ∩ <t> = 1`, and suppose
`g` has infinite order. Then `H = <g,t>` is abelian, and `(i,j) -> g^i t^j` is
injective: `g^i t^j = 1` gives `g^i = t^-j ∈ <g> ∩ <t>`. So `H ≅ Z^2`. Fix
`S`-words `w_g, w_t` for `g, t` and put `W = max(|w_g|,|w_t|)`.

For a left coset `c = xH` we use *core coordinates* `(i,j) -> x g^i t^j`. The
choice of `x` is not equivariant, but it is used only inside proofs. Two points
`u,u' ∈ c` have `u^-1 u' = g^a t^b ∈ H`. Put `|u^-1u'|_H = max(|a|,|b|)`. This
is intrinsic, and it is invariant under left multiplication.

**Parameters.** `L >= 2` is an integer, `m = floor(L/2)`, `K = 3`,
`delta = min(1, K/m^2)`, and `eta ∈ (0,1)`.

**Randomness.** Independent iid uniform labels:

* `zeta_u` for `u ∈ Gamma`;
* `lambda_(v,s)` for `(v,s) ∈ Gamma × S`;
* tie-breaking labels `beta_x` for `x ∈ Gamma`.

`Gamma` acts on each index set freely, by left multiplication on the first
coordinate. So every construction below that is an equivariant measurable
function of the labels is a factor of iid (FIID).

## Step 1 (crosses)

`u` is *occupied* if `zeta_u < delta`. Its *cross* is

`X(u) = P(u g^-L, w_g^(2L)) ∪ P(u t^-L, w_t^(2L))`.

This is a connected subgraph of `G` with at most `2(2LW+1)` vertices. Its
*core* `X(u) ∩ uH` contains the arm `{u g^i : |i| <= L}` and the arm
`{u t^j : |j| <= L}`. Moreover `gX(u) = X(gu)`.

**Intersection rule.** If `u,u' ∈ c` with `|u^-1 u'|_H <= L`, say
`u' = u g^a t^b`, then `u g^a = u' t^-b` lies on the `g`-arm of `u` and on the
`t`-arm of `u'`. So `X(u) ∩ X(u') ≠ ∅`.

## Step 2 (the coset spine `L_c`)

For a coset `c`, let `D_c` be the graph on the occupied points of `c` in which
`u ~ u'` iff `|u^-1 u'|_H <= L`. By construction `gD_c = D_(gc)` (as functions
of the shifted labels).

**Claim 2.1.** A.s., for every coset `c`, `D_c` has exactly one infinite
component `Q_c`.

*Proof.* Fix `c`. In core coordinates `D_c` is Bernoulli(`delta`) site
percolation on the transitive amenable graph `Z^2_L` (vertices `Z^2`, edges
between points at ell-infinity distance in `[1,L]`). Burton–Keane gives at most
one infinite cluster: Bernoulli site percolation on an amenable transitive
graph has at most one infinite cluster a.s. (Burton–Keane, Comm. Math. Phys.
121 (1989); Lyons–Peres, *Probability on Trees and Networks*, Chapter 7, in the
insertion-tolerant invariant form, which covers site percolation).

For existence, tile `Z^2` by the boxes `B_(p,q) = [pm, pm+m) × [qm, qm+m)`. A
box is *good* if it contains an occupied point. Boxes are disjoint, so good
boxes form Bernoulli site percolation on `Z^2` with parameter

`1 - (1-delta)^(m^2) >= 1 - e^(-delta m^2) = 1 - e^-3 > 0.95`

when `delta = 3/m^2 <= 1`. When `delta = 1` all boxes are good. Occupied points
in the same box, or in two `Z^2`-adjacent boxes, are at ell-infinity distance at
most `2m-1 <= L`, so they are adjacent in `D_c`.

*Peierls.* Let `q = 1-p <= e^-3 < 0.05` be the probability that a box is bad.
If the good cluster of the box `B_(0,0)` is finite and the box is good, some
`*`-connected (8-neighbour) circuit of bad boxes surrounds it. A circuit of
length `k` surrounding the origin meets the positive horizontal axis within
distance `k`, so there are at most `k·8^k` of them. Hence

`P(B_(0,0) good, its cluster finite) <= sum_(k>=8) k 8^k q^k <= sum_(k>=8) k 0.4^k < 0.02`,

and `P(B_(0,0) in an infinite good cluster) >= 1 - 0.05 - 0.02 > 0`. Choosing
one occupied point per box along an infinite good path gives an infinite path
in `D_c`. The event "`D_c` has an infinite component" is invariant under the
ergodic `H`-shift of `(zeta_u)_(u ∈ c)`, so it has probability `1`. Countably
many cosets give the a.s. statement. ∎

Put `L_c = ∪_(u ∈ Q_c) X(u)` and `core(L_c) = V(L_c) ∩ c`. By the intersection
rule, and because every cross is connected, `L_c` is connected, and it is
infinite. `L_c` is an equivariant function of `zeta`: `gL_c = L_(gc)`.

**Claim 2.2.** A.s., for every coset `c` and every `v0 ∈ c`, the set
`Y0 = v0<t> ∩ core(L_c)` is infinite.

*Proof.* Since `t` is central, left multiplication by `t^k` maps `v0 t^j` to
`v0 t^(j+k)` and fixes `c`, since `t^k x H = x t^k H = xH`. So `Y0` is a random
subset of the line `v0<t>`, and its law is invariant under `<t>`, which acts
freely and transitively on the line. The `<t>`-action on the iid label space is
a Bernoulli shift over free orbits, so it is mixing and hence ergodic. The event
`{Y0 ≠ ∅}` is `<t>`-invariant. By translation invariance of site percolation on
`Z^2_L` and Claim 2.1, `P(v0 ∈ Q_c) > 0`, so `P(Y0 ≠ ∅) > 0`, and by ergodicity
this probability is `1`. By Lemma 0, `Y0` is then infinite. ∎

## Step 3 (connectors)

For `v ∈ Gamma` and `s ∈ S`, let `c = vH` and `c' = vsH`. Put
`r(v,s) = d_G(vs, core(L_(c')))`, which is finite by Claim 2.1. If
`v ∈ core(L_c)` and `lambda_(v,s) < eta/(r(v,s)+1)`, add the edge `{v,vs}` and
one geodesic from `vs` to a nearest point of `core(L_(c'))`. Choose the geodesic
by lexicographically minimal tie-breaking labels along it, which is a.s. unique
and equivariant. Let `C` be the union of all added connectors, and put

`Lam = ∪_c L_c ∪ C`.

`Lam` is an equivariant measurable function of `(zeta, lambda, beta)`, so it
is FIID.

**Claim 3.1 (linking).** A.s., for every `v0 ∈ Gamma` and `s ∈ S`, the graphs
`L_(v0 H)` and `L_(v0 s H)` lie in one component of `Lam`.

*Proof.* Fix `v0, s`, and put `c = v0H` and `c' = v0sH`. For `k ∈ Z`,
centrality gives `v0 t^k s = v0 s t^k ∈ c'`. So every `v ∈ v0<t>` has
`vsH = c'`. For `R >= 0` let

`Y_R = {v ∈ v0<t> ∩ core(L_c) : r(v,s) <= R}`.

`Y_R` depends only on `zeta`, and `t^k Y_R = Y_R` in law (both cosets are
`t`-fixed). By Lemma 0 it is infinite on `E_R = {Y_R ≠ ∅}`. The union of the
`E_R` over `R` is `{Y0 ≠ ∅}`, which has probability one by Claim 2.2.

Condition on `zeta`. On `E_R`, the labels `lambda_(v,s)` for `v ∈ Y_R` are
independent of `zeta` and of each other. Each gives a connector with probability
at least `eta/(R+1)`, and there are infinitely many of them. So a.s. some
connector joins a vertex of `core(L_c)` to `core(L_(c'))`. ∎

**Claim 3.2.** `Lam` is a.s. connected and infinite.

*Proof.* Every connector meets some `L_c`. Given cosets `c ≠ c''`, pick
`v ∈ c`, `v'' ∈ c''` and an `S`-path `v = v_0, v_1 = v_0 s_1, ..., v_n = v''`.
By Claim 3.1 applied to each `(v_i, s_(i+1))`, which is a countable family,
consecutive `L_(v_i H)` lie in one component. ∎

## Step 4 (density)

*Crosses.* `o ∈ X(u)` forces `u = o·p^-1`, where `p` ranges over the at most
`2(2LW+1)` endpoints of prefixes of the two cross words. So
`P(o ∈ ∪_c V(L_c)) <= 2(2LW+1) delta <= 2(2LW+1)·3/floor(L/2)^2`, which tends
to `0` as `L -> infinity`.

*Connectors.* A connector at `(v,s)` has at most `r+2` vertices. Send mass `1`
from `v` to each of them. The expected mass sent from `o` is at most
`sum_s E[(eta/(r+1))(r+2)] <= 2|S| eta`. By the MTP,
`P(o ∈ V(C)) <= 2|S| eta`.

So `P(o ∈ V(Lam)) <= 6(2LW+1)/floor(L/2)^2 + 2|S| eta`, which can be made
below any `eps > 0`. ∎

## Examples in class Z

* `Lambda x Z` for `Lambda` nonamenable, finitely generated, with an element of
  infinite order. Theorem B of `fpbs-soft-collapse-iff-invariant-sparse-spines`
  already gives invariant spines here; the new construction is FIID.
* `Gamma~_n = p^-1(Sp_2n(Z))`, `n >= 2`, from
  `deligne-universal-cover-lattice-is-non-rf-kazhdan`. `t` is a generator of
  `ker p = pi_1(Sp_2n(R)) ≅ Z`, which is central by item 1 there. Take `g` to be
  any lift of an infinite-order `h ∈ Sp_2n(Z)`, for example a unipotent
  elementary matrix. If `g^k ∈ <t> = ker p` then `h^k = 1`, so `k = 0`. The group
  is nonamenable because it surjects onto `Sp_2n(Z)`, which contains `F_2`. It
  has property (T) by item 3 there. Since `H^1(Gamma~_n; R) = 0`, it has no
  surjection onto `Z`, so Theorem B does not apply.

## Calibration

* *Spines force cost one.* `fpbs-sparse-spine-cost-bound` converts FIID spines
  of density `eps` into `C^* <= 1 + (d/2-1)eps`. For `Gamma~_n` this reproduces
  fixed price one, which is already known by Gaboriau's theorem for groups with
  an infinite amenable normal subgroup (here the centre). Nothing contradicts
  Lyons or Gaboriau.
* *The construction does not reach `F_2`, as it must not.* `F_2` has fixed
  price two, so it has no FIID sparse spines. It also has no central element of
  infinite order. The argument uses centrality exactly twice: in Claim 2.2,
  where `t` fixes the coset, and in Claim 3.1, where `v0 t^k s = v0 s t^k`.
