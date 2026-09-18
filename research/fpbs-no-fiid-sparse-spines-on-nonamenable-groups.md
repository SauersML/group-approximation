---
rg: 2
id: fpbs-no-fiid-sparse-spines-on-nonamenable-groups
kind: claim
title: No finitely generated nonamenable group has arbitrarily sparse factor-of-iid connected infinite subgraphs
root: true
refuted_by:
  - fpbs-central-z2-groups-have-fiid-sparse-spines
  - fpbs-fiid-spines-lift-via-infinite-conjugate-intersection
distinct_from:
  fpbs-kazhdan-sparse-spines: that asserts the opposite for every infinite Kazhdan group, so at most one of the two claims is true
  fpbs-fixed-price-one-percolation-kernel: that asks for p_c < p_u directly on fixed-price-one groups; this asks for the absence of a specific factor-of-iid object, which is sufficient for it but may be strictly stronger
  fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups: that builds invariant, not factor-of-iid, spines on large classes; they do not contradict this claim
---

**OPEN (root).** For every finitely generated nonamenable group `Gamma` and
finite symmetric generating set `S`, there is `eps > 0` such that every
factor-of-iid random subgraph of `Cay(Gamma,S)` that is a.s. connected and
infinite has `P(o in V(L)) > eps`. By part (ii) of
`fpbs-fiid-soft-collapse-iff-fiid-sparse-spines`, this does not depend on `S`.

## What it gives and what already holds

* **It implies the goal.** By Corollary D of
  `fpbs-fiid-soft-collapse-iff-fiid-sparse-spines`, it gives `p_c < p_u` on
  every Cayley graph of every nonamenable group
  (route `fpbs-benjamini-schramm-via-no-fiid-sparse-spines`).
* **Soft methods must prove it.** By Corollary E of that node, any argument
  for `p_c < p_u` on `Gamma` that uses only
  - Bernoulli facts at `p <= p_c`,
  - the soft axioms (S1)--(S4), and
  - properties shared by factors of Bernoulli shifts (spectral containment in
    `infinity · lambda`, strong ergodicity, cost monotonicity)

  proves this claim for `Gamma`.
* **It holds outside fixed price one.** If `C^*(Gamma) > 1`,
  `fpbs-sparse-spine-cost-bound` gives `C^*(Gamma) <= 1+(d/2-1)theta` for the
  density `theta` of any FIID spine. So densities below
  `(C^*(Gamma)-1)/(d/2-1)` are impossible. The open content is exactly the
  fixed-price-one class.
* **It may be false without refuting the goal.** FIID sparse spines do not
  obviously force `p_c = p_u` on any Cayley graph. A group with FIID sparse
  spines would kill this route and every Bernoulli-weakly-contained soft
  argument on that group, but it would not settle `p_c < p_u` there.

## Attempts

* **Rule out spines built from sheets over a quotient.** For `pi: Gamma -> Z`
  with kernel `N`, Theorem B of `fpbs-soft-collapse-iff-invariant-sparse-spines`
  builds invariant spines as unions of whole sheets over a random height set.
  **Proved dead as an FIID construction:** Proposition F of
  `fpbs-fiid-soft-collapse-iff-fiid-sparse-spines` shows that any FIID height
  set on which `Gamma` acts through `pi` is `N`-invariant. Since `N` is
  infinite and acts mixingly, the set is a.s. `∅` or `Z`. Any spine containing
  whole fibres over a nontrivial height set has a factor through `Z` and is not
  even weakly contained in Bernoulli.
  - *Invariant:* an `N`-invariant factor.
  - *Step:* choosing the levels.
  - A periodic sheet pattern, heights fixed mod `r`, fails in the same way. It
    would give an eigenfunction `exp(2 pi i h/r)` of the mixing shift.

  So FIID spines must break the kernel symmetry at every scale, which is what
  the Hutchcroft--Pete remark that their spines are far from FIID says
  informally.
* **Prove it from spectral data of the spine process.** The hope is that the
  spectral gap or strong ergodicity of an FIID spine process forces its density
  to stay bounded below. **Where it dies:** these data do not depend on the
  process.
  - Every factor of a Bernoulli shift over `V ⊔ E` has Koopman representation
    on `L^2_0` contained in `infinity · lambda`, with spectral radius bound
    `rho` for the random-walk operator.
  - Every such factor is strongly ergodic.

  So an FIID spine of density `eps` satisfies exactly the same spectral bounds
  as `xi_p` for any `p`, or as an FIID set of density one half. The separating
  input must use the exact factor structure together with connectivity of an infinite
  set, which is not a finite-window statistic. It cannot be a
  representation-theoretic invariant.
* **Look for a counterexample in anisotropic Bernoulli percolation.** On
  `Cay(Lambda x Z)`, independent parameters `(a,b)` on the `Lambda`- and
  `Z`-edges give FIID percolations. They are `Gamma`-invariant and insertion
  tolerant, so the BLPS argument gives `theta = 0` on the critical curve. A
  point of that curve where the uniqueness curve meets it would give FIID sparse spines, by the argument of part (i) of
  `fpbs-fiid-soft-collapse-iff-fiid-sparse-spines`, without any isotropic
  `p_c = p_u`. **Status:** not decided. Grimmett--Newman nonuniqueness on
  `T_d x Z` covers only large `d`, and no source read here locates the
  uniqueness curve near the critical curve for small tree parameter.
* **Referee counterexample on `F_2 x Z^2` (2026-09-17, lens 3, verdict
  c5278109; not yet refereed itself).** Take `S = S_{F_2} ∪ {±e_1, ±e_2}`. In
  each coset `hZ^2`, open `Z^2`-edges independently with probability
  `b > 1/2`; by Harris--Kesten and uniqueness each fibre has a unique infinite
  cluster `G_h` of density `theta_{Z^2}(b)`. For `s in S_{F_2}`, add the edge
  `{(h,z),(hs,z)}` when both ends lie in giants and an iid label is below
  `a > 0`. The union `L` is FIID, and it is connected because for adjacent
  fibres the link indicator in `z` is a factor of a `Z^2` Bernoulli shift with
  mean `theta^2 a > 0`. Its density `theta_{Z^2}(b) -> 0` as `b -> 1/2`. So the
  claim is false as stated on groups with a normal `Z^2` factor, the route
  `fpbs-benjamini-schramm-via-no-fiid-sparse-spines` is dead there, and the
  same fibre-giant idea gives FIID spines on `Lambda x Z^2`, which bypasses
  the anisotropic `Lambda x Z` attempt above. Lens 3 also notes that "the BLPS
  argument gives `theta = 0` on the critical curve" is applied to a
  non-isotropic model without a source.
* **Refuted (2026-09-17, swarm-0917-w7-w7-bs-last1, minimal-counterexample).**
  The claim is false, and false on a large class that includes Kazhdan groups.
  - `fpbs-central-z2-groups-have-fiid-sparse-spines` (ESTABLISHED) already
    gives FIID sparse spines on the nonamenable groups `F_2 x Z` and
    `Gamma~_n`. This subsumes the lens 3 example above.
  - `fpbs-fiid-spines-lift-via-infinite-conjugate-intersection` (ESTABLISHED,
    agent-verified) lifts FIID spines from a finitely generated `H` to any
    `Gamma` generated by `{g : |H ∩ gHg^-1| = ∞}`. Put an FIID `H`-spine in
    each left coset and link neighbouring coset spines along the infinite
    contact set `x(H ∩ sHs^-1)`, where `Bernoulli` mixing of that subgroup
    forces a link. This gives centreless members `F_2 x F_2` and `SL_n(Z)`
    for `n >= 3`, via `Z^{n-1} ⊲ Stab(e_1)`, and then `Stab(e_1) ∩ Stab(ge_1)`,
    which contains infinitely many transvections.
  - *Consequence.* The route `fpbs-benjamini-schramm-via-no-fiid-sparse-spines`
    is dead. Its other prerequisite, `fpbs-fiid-soft-collapse-iff-fiid-sparse-spines`,
    is now ESTABLISHED via `fpbs-sheet-spines-not-weakly-contained-in-bernoulli-proof`.
    So Corollary E applies: on these groups no soft argument that stays
    weakly contained in Bernoulli proves `p_c < p_u`.
    - *Invariant:* FIID sparse spines.
    - *Step where it dies:* the continuation `p_c -> p_c + eps`.
  - *What survives.* The restricted statement "no FIID sparse spines on
    nonamenable groups without a finitely generated subgroup `H` with FIID
    spines and `Σ_H` generating" is still open. Its test cases include the
    fixed-price-one survivors of `fpbs-fixed-price-one-percolation-kernel`:
    torsion Tarski monsters and free Burnside groups.
