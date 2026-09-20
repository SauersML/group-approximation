---
rg: 2
id: monster-bc-failure-at-measured-coefficient-is-the-module-crux
kind: claim
title: The module route reduces to whether an expander monster fails Baum--Connes at a measured module-dual coefficient; for a triple defect the proper-orbit and tracial detectors are excluded and the maximal-versus-reduced comparison remains a conditional approach
distinct_from:
  some-nonexact-group-has-a-k-inexact-module-triple: that is the open existence of the K-defect; this isolates the single enabling question behind it and records detector restrictions without claiming they exhaust the possible approaches.
  module-defect-needs-non-k-exact-host: that is the established necessary condition on the host (fails Baum--Connes with coefficients); this is the open sufficient-direction crux, once such a host is fixed.
  module-dual-actions-have-no-wandering-open-sets: that excludes the proper-orbit (ghost) detector; this records what detector remains after that exclusion and the tracial one.
---

**OPEN.** Fix an expander-monster host `G` failing Baum--Connes with coefficients
(`osajda-monster-hosts-for-bc-module-route`, items (1),(2); item (4) is not a verified host, see
`osajda-rf-relator-covers-are-not-expanders`); by
`module-defect-needs-non-k-exact-host` this is forced. The module route
(`bc-counterexample-via-module-k-inexactness`) then turns on:

> **(Q)** Does the Baum--Connes-with-coefficients failure of `G` already occur at a **measured**
> module-dual coefficient `C(V^)` -- one carrying a `G`-invariant probability measure of full
> support -- and in the sub/quotient form of a module triple `(V, W)`?

A "yes" builds a trivial-coefficient counterexample; a proof that measured coefficients always
satisfy Baum--Connes would kill the route.

**Why this is the whole content.**
- The known monster failures are at **Stone--Cech** coefficients: `l^inf(G) = C(βG)`, or
  `C_0(Ω_(βX))` in Finn-Sell's groupoid form (Higson--Lafforgue--Skandalis;
  `monster-bc-detector-lives-on-a-proper-orbit-ideal`).
  - These carry **no** `G`-invariant probability measure, since `G` is non-amenable. An earlier
    version said "for infinite `G`", which fails for amenable `G`; corrected 2026-09-13.
  - The witness is the expander's non-compact ghost, which dies in the corona quotient.
  - The corona coefficients over `Ω_(∂βX)` satisfy Baum--Connes (Finn-Sell Corollary 4.4).
- A module dual `X = V^` is the opposite: compact metrizable, with the invariant Haar
  probability measure of full support and no proper open orbit
  (`module-dual-actions-have-no-wandering-open-sets`). To our knowledge no counterexample to
  Baum--Connes with coefficients is known at any coefficient with an invariant faithful trace;
  the module route would be the first.

**Detectors, and which survive.**
- *Proper-orbit rank at infinity* (Higson--Lafforgue--Skandalis, Spakula arXiv:0907.2249). Dead
  for module duals: no wandering open set, no proper orbit
  (`module-dual-actions-have-no-wandering-open-sets`).
- *All bounded positive traces on the module quotient.* The
  [factorization theorem](amenable-kernel-quotient-traces-factor-reduced.md)
  and [relation-ideal identification](module-evident-ideal-is-kernel-relation-ideal.md)
  make every trace on D=C/J descend to B. Thus
  [all bounded positive traces](module-quotient-k0-defects-are-trace-invisible.md)
  kill the prospective degree-zero quotient defect, not only traces
  initially obtained from invariant measures. For torsion V a trace on C
  annihilating the ideal K_0 image also factors through B. This does not
  assert that every trace on C factors through B. Nor does it exclude
  index pairings, cyclic cocycles or unbounded semifinite traces.
  [The torus example](torus-has-nonzero-k0-class-invisible-to-every-trace.md)
  prevents a trace-to-K-theory vanishing conclusion. Haar trace can still
  test other assembly surjectivity proposals, but at the Bernoulli
  coefficient the [product-trace theorem](bernoulli-product-traces-kill-rank-invisible-k0.md)
  kills the rank-invisible remainder.
- *Maximal-versus-reduced comparison.* The maximal coefficient sequence
  is exact, so comparison of its six-term sequence with the reduced maps
  remains a possible approach. It is not equivalent to finding a maximal
  degree-zero class unless a maximal-to-reduced K-theory lift is supplied;
  that lift is additional data, and the original defect may be in degree
  one. The unconditional equivalent formulation is instead
  [a nonzero liftable quotient-kernel class](some-module-quotient-has-a-nonzero-liftable-kernel-class.md)
  in K_j(C/J), with zero six-term boundary in K_(j−1)(J).
- *Unital coefficient embeddings.* The
  [faithful-trace embedding restriction](equivariant-faithful-trace-embeddings-force-measure.md)
  requires an invariant full-support probability measure. It excludes
  an infinite family of disjoint translates of a nonempty open set for
  embeddings into faithfully traced algebras with trace-preserving action,
  including reduced group algebras under conjugation. This is not a
  blanket exclusion of multiplier or semifinite constructions.

## Attempts

- **Bernoulli candidate.** `V = F_p[G]`, `X = (Z/p)^G` the full shift, `W = ker(F_p[G] ->
  F_p[G/H])` for `H <= G` infinite, so `Z = (Z/p)^(G/H)` is the subshift of configurations
  constant on left `H`-cosets and `V ⋊ G = F_p wr G`. This is a survivor of
  `split-quotients-give-exact-reduced-crossed-products` (part (D)): no equivariant c.p.
  splitting, `G` not co-amenable in the quotient. The window-defect criterion
  (`window-defect-forces-module-triple-inexactness`) asks for locally admissible patches of the
  coset-subshift that do not glue globally, where a boundary-gapped `D` has an approximate
  kernel. This can be arranged at the **C*-level** by importing the expander into the window (as
  in that node's non-module model `(βG, ∂βG)`), but the resulting witness `f(D)` is a positive
  element, and computing its **K-class** in `K_0(C(X) ⋊_r G)` -- and showing that class survives
  in `ker q_*^r / im i_*^r` -- is exactly the missing step.
- **Where it dies.** The C*-defect is a single non-exactness witness, not a projection with a
  computed K-class. The max-vs-reduced comparison would compute it, but no invariant on
  `K_0(C(X) ⋊_max G)` is known that (a) is nonzero on the Kazhdan-type class and (b) vanishes on
  the reduced ideal image. Traces are excluded above; the proper-orbit index is excluded by the
  geometry. A genuinely new, non-tracial, boundary-type index adapted to a compact **measured**
  system is what is missing.
- **Residually finite handle, untested and currently without a host.**
  - The idea: for a residually finite host with congruence quotients `G/N_i`, the reduced trace of
    a gapped spectral projection is a limit of finite eigenvalue fractions. That mechanism is
    recorded for the group algebra in `bc-kun-thom-gap-label-is-congruence-eigenvalue-limit`.
    Whether the analogous congruence approximation computes the **max-vs-reduced** comparison for
    the module coefficient `C((Z/p)^G)`, rather than a trace, is unexplored.
  - **No host (2026-09-13).** An earlier version pointed to Osajda's residually finite non-exact
    groups (host item (4)).
    - Their relators are Z/2-homology covers, which never form an expander family
      (`osajda-rf-relator-covers-are-not-expanders`).
    - No known theorem makes them fail Baum--Connes with coefficients, and by
      `module-defect-needs-non-k-exact-host` a host must fail it.
  - So the handle needs a residually finite group containing a weakly or coarsely embedded
    expander. This lane knows of none; the check is bounded to HLS02, Willett--Yu I, Finn-Sell
    arXiv:1401.6841 and Osajda arXiv:1703.03791.
- **The kill through measured coefficients contains trivial-coefficient Baum--Connes.**
  - Consider a theorem that Baum--Connes holds at every coefficient `C(X)` whose compact `G`-space
    carries an invariant probability measure of full support. The one-point space with its Dirac
    measure qualifies, so the theorem includes trivial coefficients for the host `G`. For an
    expander monster that case is open. Willett--Yu I (arXiv:1012.4150, p. 5, read from the text
    extraction) write "here little is known about the usual (reduced) assembly map".
  - Restricting to dual-module coefficients is no easier. By item 2 of
    `amenable-kernel-bc-transfer-and-ktop-half-exactness`, injectivity (resp. surjectivity) of
    `mu_(G, C(V^))` is equivalent to injectivity (resp. surjectivity) of trivial-coefficient
    assembly for `V ⋊ G`.
  - So (Q) failing for every `V` is trivial-coefficient Baum--Connes for all groups `V ⋊ G`, and
    `V = 0` gives `G` itself. (Q) holding for some `V` is a counterexample for that `V ⋊ G`. The
    dual-module crux is the root restricted to these groups.
  - Hence no kill of the route can pass through assembly without settling trivial-coefficient
    Baum--Connes for the host. A kill must prove K-exactness of module triples directly, by an
    exactness mechanism that never identifies the K-theory.
  - The mechanisms recorded so far all need an equivariant splitting, a finite quotient or a
    co-amenable section (`split-quotients-give-exact-reduced-crossed-products`), and the
    Bernoulli survivors above have none of them.
- **At the Bernoulli coefficient, (Q) is the host plus one comparison map (2026-09-13).**
  `bernoulli-bc-splits-into-host-and-cylinder-comparison` (established):
  - Take `V = F_p[Z]` for a `G`-set `Z` with finite point stabilizers, `X = (Z/p)^Z`,
    `I_1 = C_0(X \ {0})`. Then `mu_(G, C(X)) = mu_G ⊕ mu_(G, I_1)`, through the fixed point `0`.
  - `K^top_*(G; I_1)` is computed for **every** `G`: the Chakraborty--Echterhoff--Kranz--Nishikawa
    weak K-equivalence plus going-down.
  - `mu_(G, I_1)` is surjective (resp. injective) iff one reduced comparison map `T_r` is.
  - For torsion-free `G` this says the cylinder projections form a free basis of `K_0(I_1 ⋊_r G)`
    and `K_1(I_1 ⋊_r G) = 0`.
  - `T_r` is an isomorphism modulo every finite support level. So a Bernoulli witness beyond the
    host lives in configurations of unbounded support, where a monster's expander markings sit.
  - Where it stops: nothing computes `T_r` over an expander monster. `T_r` is always injective
    (`bernoulli-assembly-injective-beyond-the-host`). Its surjectivity is the open
    `bernoulli-cylinder-comparison-fails-for-some-group`, which routes into the root by
    `bc-counterexample-via-bernoulli-cylinder-defect`.
