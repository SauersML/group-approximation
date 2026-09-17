---
rg: 2
id: fpbs-soft-collapse-iff-invariant-sparse-spines
kind: claim
title: A monotone invariant family equal to Bernoulli up to p_c can collapse above p_c exactly when invariant sparse spines exist, and they exist over every Z-quotient with finitely generated kernel
distinct_from:
  fpbs-fiid-partition-spectral-jump-model: that model merges label classes that are not graph-connected and only reproduces spectral data; this family is a genuine bond percolation that equals Bernoulli for all t<=p_c and has a unique infinite cluster for every t>p_c
  fpbs-unimodular-critical-quotients-can-have-zero-pu: that is a unimodular quotient multigraph; this lives on the fixed Cayley graph itself and keeps the exact Bernoulli law through p_c
  fpbs-sparse-spine-cost-bound: that turns an FIID spine into a cost bound; this turns invariant (not necessarily FIID) spines into a collapsed monotone family and back
---

**ESTABLISHED (class-killing obstruction).** Proof in
`fpbs-soft-collapse-iff-invariant-sparse-spines-proof`.

Let `Gamma` be an infinite nonamenable finitely generated group, `S` a finite
symmetric generating set, `G = Cay(Gamma,S)`, and `(xi_t)` the standard
coupling of Bernoulli bond percolation, `xi_t = {e : U_e <= t}`.

**Soft collapse family.** A probability-preserving `Gamma`-system with
equivariant bond configurations `omega_t`, `t in [0,1]`, such that

* (S1) `omega_s ⊆ omega_t` for `s <= t`;
* (S2) `(omega_t)_{t <= p_c}` has the joint law of `(xi_t)_{t <= p_c}`;
* (S3) the system is ergodic and every `omega_t`, `t>0`, is insertion tolerant;
* (S4) for every `t > p_c`, `omega_t` has exactly one infinite cluster a.s.,
  and `theta(t) = P(o in infinite cluster of omega_t) -> 0` as `t ↓ p_c`.

**Invariant sparse spines.** For every `eps > 0` there is a random subgraph
`L` of `G` with `Gamma`-invariant law that is a.s. connected and infinite and
has `P(o in V(L)) <= eps`.

**Theorem A.** `G` carries a soft collapse family if and only if it has
invariant sparse spines.

**Theorem B.** If there is a surjection `pi: Gamma -> Z` whose kernel is
finitely generated, then `Cay(Gamma,S)` has invariant sparse spines for every
`S`. So it carries a soft collapse family.

**Corollary C (obstruction).** These are concrete Cayley graphs with a true
nonuniqueness window:

* `T_3 x Z = Cay((Z/2*Z/2*Z/2) x Z)`, by Hutchcroft's nonunimodular theorem;
* `pi_1` of a closed hyperbolic 3-manifold fibring over the circle, a surface
  group by `Z`, which is hyperbolic;
* `F_2 x Z` with the Pak--Smirnova-Nagnibeda generating sets.

Each of them also carries a family satisfying (S1)--(S4). Hence no argument
can prove `p_c < p_u` if its inputs are only (a) facts about Bernoulli
percolation at parameters `p <= p_c`, including sharpness, tail bounds, critical
no-percolation and the critical L2 bound, and (b) the supercritical properties
invariance, ergodicity, insertion tolerance, monotonicity, uniqueness for
`t > p_c` and continuity of `theta` at `p_c`. Such an argument would give
`p_u = p_c` for these families as well as a window, a contradiction.

Exact failing step: the continuation from `p_c` to `p_c + eps`. Every
invariant percolation with a unique infinite cluster has
`||T||_{2->2} >= theta^2 |B_R| -> infinity`, by Jensen on `|I ∩ B_R|`. On the
hyperbolic fibred examples the family therefore has `||T_{p_c}||_{2->2} <
infinity`, by `fpbs-hyperbolic-nonunimodular-critical-l2-gap`, but
`||T_t||_{2->2} = infinity` for every `t > p_c`. So the step in
`fpbs-critical-l2-implies-nonuniqueness` that passes from `p_c` to a larger
parameter, and likewise any "collapse forces a contradiction" argument, must
use a supercritical property this family lacks. For `t > p_c` the family is
not a product measure (so Russo, BK and submultiplicativity are unavailable)
and deletion tolerance is not claimed. With product generators it fails: a
selected sheet `N x {h}` cannot lose a single edge. Harris--FKG is not decided
here.

Consistency check (calibration): by the spine cost argument of
`fpbs-sparse-spine-cost-bound`, applied to the free action obtained by taking
the product with Bernoulli, invariant sparse spines force cost one. The groups
of Theorem B have fixed price one (Gaboriau, infinite finitely generated
normal subgroup of infinite index), so nothing contradicts Lyons. For `F_2`,
which has fixed price two, no surjection to `Z` has finitely generated kernel
and no soft collapse family exists, as Lyons' argument demands.

Paradigm answers:

* **Why this works where earlier attempts failed.** It changes the object: the
  Bernoulli supercritical law is replaced by a coupled invariant collapse,
  instead of trying to estimate that law.
* **First falsifiable step.** Connectivity of the levelled sheet spines, and
  `theta -> 0` by per-vertex Borel--Cantelli.
* **Calibration.** Lyons' cost theorem on `F_2`, as above.

What remains open: whether every fixed-price-one nonamenable group has
invariant sparse spines. That would kill soft arguments on the whole Lyons
kernel `fpbs-fixed-price-one-percolation-kernel`. Kazhdan groups and
higher-rank lattices are the natural next test.
