---
rg: 2
id: fpbs-fiid-soft-collapse-iff-fiid-sparse-spines
kind: claim
title: A factor-of-iid soft collapse family exists exactly when the group has factor-of-iid sparse spines, and a group without them has p_c < p_u on every Cayley graph
distinct_from:
  fpbs-soft-collapse-iff-invariant-sparse-spines: that is the invariant version and its spine constructions (sheets over a Z-quotient) are not weakly contained in Bernoulli, so it does not kill arguments that use spectral gap, strong ergodicity or cost monotonicity; here the whole family is a factor of iid, the spine condition is a group property, and it gives a sufficient condition for p_c < p_u
  fpbs-kazhdan-sparse-spines: that is an open existence target for factor-of-iid spines on Kazhdan groups; here the existence of such spines is shown to be exactly what blocks Bernoulli-weakly-contained soft arguments
  fpbs-non-fixed-price-one-has-nonuniqueness: Lyons' theorem (proved in the archive through the route fpbs-threshold-collapse-forces-price-one) also follows from part (i) with the spine cost bound; part (iii) and Corollaries D and E are new
---

**OPEN** (set back from ESTABLISHED on 2026-09-17, after referee lenses 1
and 3 refuted parts of the node; see Attempts). Proof attempt in
`fpbs-fiid-soft-collapse-iff-fiid-sparse-spines-proof`, which now takes the
corrected second bullet of Proposition F as the open prerequisite
`fpbs-sheet-spines-not-weakly-contained-in-bernoulli`.

Let `Gamma` be an infinite nonamenable finitely generated group, `S` a finite
symmetric generating set, `G = Cay(Gamma,S)`, and `xi_t = {e : U_e <= t}` the
standard monotone coupling of Bernoulli bond percolation.

**Factor of iid (FIID).** A random object on `G` is FIID when it is a
`Gamma`-equivariant measurable function of an iid uniform field indexed by
`V(G) ⊔ E(G)`. The same class arises from vertex labels alone, because each
vertex label splits into countably many independent uniforms.

**FIID sparse spines on `G`.** For every `eps > 0` there is an FIID random
subgraph `L` of `G` that is a.s. connected and infinite, with
`P(o in V(L)) <= eps`.

**FIID soft collapse family.** A family `(omega_t)_{t in [0,1]}` satisfying
(S1)--(S4) of `fpbs-soft-collapse-iff-invariant-sparse-spines`, such that the
whole family `(U, (omega_t)_t)` is one FIID process. So `omega_t = xi_t` for
`t <= p_c` pointwise, not only in law.

**Theorem.**

* (i) If `p_c(G) = p_u(G)`, then `G` has FIID sparse spines.
* (ii) Having FIID sparse spines does not depend on `S`. Write
  "`Gamma` has FIID sparse spines".
* (iii) `G` carries an FIID soft collapse family if and only if `Gamma` has
  FIID sparse spines.

**Corollary D (sufficient condition).** If `Gamma` has no FIID sparse spines,
then `p_c < p_u` on every Cayley graph of `Gamma`. If `Gamma` has FIID sparse
spines, then `Gamma` has fixed price one, by `fpbs-sparse-spine-cost-bound` and
`fpbs-bernoulli-maximal-cost`.

**Corollary E (obstruction, invariant: FIID sparse spines).** Every
FIID family is a factor of a Bernoulli shift. So its Koopman representation on
`L^2_0` is contained in `infinity · lambda`, it is mixing and strongly ergodic,
and its free extensions that are themselves FIID have cost at least
`C^*(Gamma)` (for arbitrary free extensions this would need fixed price). Suppose an argument
proves `p_c(G) < p_u(G)` using only:

* (a) facts about Bernoulli percolation at `p <= p_c`;
* (b) (S1)--(S4);
* (c) properties shared by all factors of Bernoulli shifts, such as those just
  listed.

On a group with FIID sparse spines, such an argument would apply to the family
of (iii), whose uniqueness threshold is `p_c`. That is a contradiction. So
running the argument on `Gamma` proves that `Gamma` has no FIID sparse spines.
So every soft argument that exploits weak containment in Bernoulli, applied to
a class of groups, proves the open hole
`fpbs-no-fiid-sparse-spines-on-nonamenable-groups` for that class.

**Proposition F (the known invariant spines are not FIID).** Let
`pi: Gamma -> Z` be onto, with kernel `N`.

* Any FIID random subset `H ⊆ Z` on which `Gamma` acts through `pi` is a.s.
  `∅` or `Z`.
* Every invariant spine that contains `pi^-1(h)` exactly for `h` in a random
  set `H ≠ ∅, Z` has a nontrivial factor on which `Gamma` acts through `Z`.
  Hence it is not weakly contained in Bernoulli. When the law of `H` is
  atomless it is also not strongly ergodic. (The earlier unrestricted claim
  "not strongly ergodic" is false in the atomic case; see Attempts.)

This applies to the sheet spines of Theorem B of
`fpbs-soft-collapse-iff-invariant-sparse-spines`, whose height sets are
Bernoulli and atomless. So the obstruction of that node does not reach
arguments of type (c).

## Attempts

* **Referee audit, 2026-09-17 (swarm-0917): set back to OPEN.**
  * *Lens 1 (refuted, verdict 64891fab).* The second bullet of Proposition F
    does not follow in the atomic case. The proof only shows that the
    finite-index subgroup `pi^-1(rZ)` has a nontrivial invariant set, but a
    `Gamma`-action on the finite transitive space `Z/r` is ergodic and
    strongly ergodic. Counterexample: `j` uniform in `Z/r`, sheets over
    `rZ + j`, connectors chosen by iid vertex labels. Its Koopman space is
    `L^2_0(Z/r) ⊗ 1 ⊕ L^2(Z/r) ⊗ L^2_0(Bern)`, and neither summand has
    almost-invariant vectors, so this spine is strongly ergodic.
    "Not weakly contained in Bernoulli" still holds, through the restriction
    to `pi^-1(rZ)`. The statement above is corrected accordingly, and the
    corrected bullet is split out as
    `fpbs-sheet-spines-not-weakly-contained-in-bernoulli`. Minor: Corollary E
    covers only FIID free extensions; also corrected above.
  * *Lens 2 (survived, verdict 9f13bc2f).* Parts (i)--(iii), Corollary D, both
    bullets of Proposition F and the Russo/Koopman diagnosis check out;
    noted the same Corollary E overstatement.
  * *Lens 3 (refuted, verdict c5278109).* Parts (i)--(iii), Corollaries D and
    E hold. The closing sentence "no group with FIID sparse spines is
    currently known" is false: on `F_2 x Z^2`, take the unique infinite
    cluster `G_h` of supercritical (`b > 1/2`) bond percolation in each
    `Z^2`-coset, and add `F_2`-edges between giants with an iid label below
    `a > 0`. This is an FIID connected infinite subgraph of density
    `theta_{Z^2}(b) -> 0` as `b -> 1/2`, consistent with Corollary D since
    that group has fixed price one. The sentence is removed above. This
    counterexample also bears on the root
    `fpbs-no-fiid-sparse-spines-on-nonamenable-groups`.
  * Parts (i)--(iii) and Corollary D were found sound by all three lenses;
    the node stays OPEN only until the split-out prerequisite is re-refereed.
