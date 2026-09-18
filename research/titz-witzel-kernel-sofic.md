---
rg: 2
id: titz-witzel-kernel-sofic
kind: claim
title: The smallest Titz--Witzel simple Kazhdan kernel is sofic
artifacts:
  - research/artifacts/titz-witzel-sofic-structure-audit-2026-08-26.md
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
distinct_from:
  titz-witzel-soficity-is-one-finite-csp: that is the established equivalence between soficity of this kernel and a marked three-permutation gate; this is the open soficity assertion itself.
  titz-witzel-exact-kazhdan-mf-radical-over-z: that proves every clause of the torsion-free exact-radical target except soficity; this is the one missing clause, for the smallest kernel.
refuted_by:
  - titz-witzel-kernel-nonsofic
---

**OPEN.**  Let `K = Gamma_1^2` be the smallest Titz Mite--Witzel lattice
(arXiv:2509.05054v2, Theorem 4.1; the index-two subgroup of the 15-generator
group of their Proposition 4.3).  It is finitely presented, torsion-free,
infinite, simple and Kazhdan.  The claim is that `K` is sofic.

Equivalent finite forms are `titz-witzel-soficity-is-one-finite-csp`,
`titz-witzel-sofic-gate-two-generators-four-approximate-relators` and
`titz-witzel-two-generator-involution-sandwich-normal-form`.

Value.  `K x Z` then closes `torsion-free-sofic-exact-mf-radical-over-z`
through `torsion-free-sofic-exact-mf-radical-via-titz-witzel`.  `K` would be
a finitely presented sofic Kazhdan group that is not residually finite
(Alekseev--Thom Open Problem 6.1).  Since `K` is isolated and not elementary
sofic, it would also answer Cornulier's Question 5 positively.

## Attempts

* **Elementary permanence.**  Dead: `titz-witzel-kernel-not-elementary-sofic`.
  No finite chain of subgroups, direct limits, marked limits and amenable
  extensions reaches `K`, and `K` is not a nontrivial marked limit.
* **Structured finite models.**  The cyclic affine, cyclic normalizer,
  central-square-lift and regular-packet ansatzes, a trivial second
  matching, and sparse surgery on exact sheets were each proved to collapse
  the mark or to keep a linear defect (the `titz-witzel-*` ansatz nodes).
* **Through the Radu sublattice.**  Soficity of `K` forces soficity of
  Radu's non-residually-finite BMW lattice, `radu-bmw-lattice-sofic`.  Its
  marked gate must keep `[y(xz)^2y, xz]` macroscopically nontrivial and must
  not factor through the horizontal tree quotient (artifact Sections 3--4).
* **Biography of a minimal counterexample: partial-action rounding (swarm-0917, inverter).** The
  one-sentence reason every cut-and-paste construction fails is ESTABLISHED in
  `kazhdan-consistent-partial-models-round-to-finite-actions`. Suppose a permutation tuple has
  consistent monodromy on a set of density `1 - eta`, meaning that every trivial word read inside
  the set closes. Globalizing the partial action and projecting with property (T) forces every
  generator to move at most `(2 + 2/kappa^2) eta n` points. This kills every model that agrees
  with a genuine `K`-set (finite, a coset space, the building, a boundary) on all but `eta n`
  points and is re-glued arbitrarily elsewhere. The invariant is the partial action on the
  agreement set, and the dying step is its globalization. A sofic model of `K` therefore has
  three forced properties.
  * (i) Its consistency deficit is at least `c_kappa` times its mark (so it is not a sparse
    re-gluing of any `K`-set).
  * (ii) Its open trivial words sit far from every relator defect, at filling radius
    `>~ log(c_kappa m/eps)/log(2|S|)` (`kazhdan-sofic-models-carry-long-scale-monodromy`), so
    fixing relators on balls (Kun, Alekseev--Drigalla, radius-`r` rigidity) supplies no mark.
  * (iii) Its commutant is non-ergodic (`kazhdan-ergodic-sofic-centralizer-forces-lef`).

  The negative direction reduces to the purely combinatorial deletion-repair statement of
  `titz-witzel-kernel-nonsofic-iff-consistent-deletion-repair`: nonsoficity holds iff every almost
  solution becomes consistent after deleting `o(n)` points. Where this approach dies: neither
  direction of (P2) is proved. A positive answer needs a model with logarithmic-scale monodromy
  that is not confined to `o(n)` points, and no construction of such a model for `K` is known.
  The unexplored recipes are non-normal (non-Galois) finite branched covers of the quotient
  complex, with inhomogeneous branching data. Galois branched covers have the same local group at
  every lift of a branch point. That suggests a linear defect, but this was checked only
  heuristically and is not recorded as a claim.
- 2026-09-17 (swarm-0917-w4-titz-sofic, branched hyperbolization): took up the
  branched-cover recipe above and turned it into an exact equivalence plus a
  decomposition.
  * Established `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`:
    `pi_1(Y_1^2)` is sofic iff there are finite branched covers with branching
    mass `beta -> 0` whose `pi_1` are sofic.  Branching is inhomogeneous in
    general, and every such cover is locally CAT(0).
  * Established `flat-hitting-branched-covers-have-hyperbolic-pi1`: if branch
    links have angular girth `> 2pi` (G) and the branch set meets every
    immersed `R`-flat disk (H), then `pi_1` is hyperbolic.  In the square case
    it is also cubulated, hence residually finite.
  * Route `titz-witzel-kernel-sofic-via-branched-hyperbolization` rests on two
    independent open prerequisites.
    - `titz-witzel-flat-hitting-sparse-branched-covers`: finite combinatorics.
    - `titz-witzel-flat-hitting-branched-cover-groups-are-sofic`: soficity of
      explicit hyperbolic groups.
  * Contrapositive route
    `nonsofic-hyperbolic-group-from-titz-witzel-flat-hitting-covers`: a
    nonsofic kernel together with the first prerequisite gives a nonsofic
    hyperbolic group.
  * For Radu's sublattice, `radu-bmw-lattice-sofic-from-flat-hitting-branched-covers`
    has a single open prerequisite, `radu-square-complex-flat-hitting-sparse-branched-covers`.
  * Where this dies for now: no branch set meeting all flats sparsely has been
    built.  Branch sets pulled back from product or height coordinates are
    ruled out, heuristically, by irreducibility.  Target stays OPEN.
- 2026-09-17 (swarm-0917, d-tfs-p2, transplanter): tried to remove the hyperbolic-group
  prerequisite from the branched-cover route and to kill its contrapositive.  **Refereeing
  refuted the statement as written**, so the enabling claim is OPEN and none of the gains below
  are currently available; they are recorded as what the repair would buy.
  * Attempted `sparse-fully-branched-covers-iff-sofic-simple-residual`.  Let `Y` be a locally
    CAT(0) 2-complex with an infinite simple finite-index subgroup `K <= pi_1(Y)`.  Then `K` is
    sofic iff there are sparse branched covers (`beta -> 0`) in which every component contains a
    branch vertex.  Equivalently, the branched components carry a fixed fraction of the sheets.
    No soficity of `pi_1(X)` is used.
    - Run Step 3 of the reduction with the trivial `pi_1(X)`-model.  This gives an almost
      homomorphism on `p^(-1)(v)`.
    - For the mark: if a deep point is fixed by every short `k in K`, the developing map is
      invariant, and it descends to a local homeomorphism `Delta/K -> X \ B` with open and
      compact image.  So that point lies in an unbranched component.
    - Simplicity (`infinite-simple-group-permutation-stable-iff-nonsofic`) finishes.
    - Converse: unbranched components are genuine `G`-sets, on which `K` acts trivially, so a
      sofic model puts only `O(epsilon n)` sheets in them.
  * (H) forbids unbranched components, because apartments immerse.  So route
    `titz-witzel-kernel-sofic-via-flat-hitting-covers` has the single open prerequisite
    `titz-witzel-flat-hitting-sparse-branched-covers`.  (G) and
    `titz-witzel-flat-hitting-branched-cover-groups-are-sofic` are redundant.
  * `nonsofic-hyperbolic-group-from-titz-witzel-flat-hitting-covers` would be invalidated.  Its
    two prerequisites would be jointly inconsistent: a nonsofic kernel means flat-hitting sparse
    covers do not exist.  This does not take effect while the enabling claim is OPEN.
  * Nonsoficity would become equivalent to a rigidity statement: every sparse branched cover of
    `Y_1^2` is, up to `o(N)` sheets, copies of `Y_1^2` and its genuine double cover.
  * Where this stops.  Two places now.  (i) The referee gap: Step B imports Step 4 of
    `sparse-branched-covers-sofic-pi1-reduction-proof`, which silently needs every vertex link of
    `Y` to be connected (free basis of `pi_1(S_y)`; `Y°` connected so `pi_1(Y°) -> G` is onto;
    each cone point's link connected and covering `Lk(y)`).  Gluing a square at a corner of
    `Y_1^2` gives a `Y'` with the same `G` and `K` but a disconnected vertex link, admitting no
    branched cover at all, so the theorem as stated would settle this target with no argument.
    The links of `Y_1^2` themselves are connected, so adding the hypothesis is expected to leave
    the corollary intact, but the repaired statement is not recorded or refereed.  (ii) Even
    then, no fully branched sparse cover has been built.  Target stays OPEN.
- 2026-09-17 (d-tw-obs, obstruction-miner, host-geometry): **Cremona hosts are dead.**
  The live spark "Cremona host for K" proposed embedding `K` in `Bir(P^n)`,
  `n >= 3`. Cremona groups are sofic (Cornulier), and Cantat--Cornulier kill
  only dimension 2.
  * Established `kazhdan-subgroups-of-cremona-groups-are-residually-finite`
    (route `kazhdan-subgroups-of-cremona-groups-rf-proof`, requires []): over
    any field and in any dimension, finitely generated Kazhdan subgroups of
    `Bir(P^n_k)` are residually finite. So neither `Gamma_1^2` nor `K` embeds in
    any Cremona group.
  * Invariant: reducing the generators modulo a large finite residue field
    gives partial actions on `P^n(F_q)` that are consistent along *every*
    trivial word (the identity principle for rational maps). They have density
    `1 - O(1/q)`.
  * Dying step: globalize the partial action and project `1_Omega` onto
    invariant vectors with property (T). Almost all points lie in finite orbits,
    where a non-trivial element must move all but `O(q^(n-1))` points. That
    yields finite quotients, which `K` does not have.
  * The same argument kills every algebraic host whose reductions are exact
    partial actions. It is a clean special case of the partial-action rounding
    above that avoids the refuted re-gluing sentence. A sofic certificate for
    `K` must come from approximations whose monodromy is inconsistent on a
    macroscopic set, not from specializing any faithful birational action.
    Target stays OPEN.
- 2026-09-17 (d-tw-ref, reframer, symmetric branched covers): turned the
  Galois heuristic above into a theorem and killed a whole construction class.
  * Established `branched-cover-branching-mass-is-quantized-by-deck-group`.
    For a connected branched cover `X -> Y` of degree `N` with deck group `D`,
    `beta(X)` is an integer multiple of `|D|/N`, and `beta(X) >= |D|/N`
    whenever `X` branches anywhere.  Galois covers have integer `beta`.
  * Since the finite residual has index 2, every sparse sequence for `Y_1^2`
    of degree `> 2` has `|D_n|/N_n <= beta_n -> 0`.
  * What dies, whatever (H) or (G) say: Galois covers, Cayley-complex models of
    finite quotients of `pi_1(Y minus vertices)`, coset covers `H` with
    boundedly many conjugates (`D = N_F(H)/H`), and any equivariant
    construction with boundedly many deck orbits on sheets.
  * The invariant is the deck-invariant local degree plus the free action on
    sheets.  The dying step is the first branch vertex, which costs `|D|`
    sheets.
  * Considered and not pursued, because already covered:
    - exhausting `R_K` by treeable or other non-(T) subrelations dies by
      `kazhdan-relations-coamenable-subrelations-locally-kazhdan`;
    - the centralizer form is `kazhdan-ergodic-sofic-centralizer-forces-lef`.
  * Not proved (heuristic only): with support in an unbranched CAT(0) ball,
    a twisting surgery on several copies of a cover cannot create a single
    branch vertex.  The punctured ball is homotopy equivalent to the link,
    and pushing loops to the boundary needs geodesic extension.  Branch
    points would have to be planted in cancelling groups.
  * No positive construction is proposed.  Target stays OPEN.
