---
rg: 2
id: monster-bc-failure-at-measured-coefficient-is-the-module-crux
kind: claim
title: The module route reduces to whether an expander monster fails Baum--Connes at a measured module-dual coefficient, and the only surviving detector is the maximal-versus-reduced comparison
distinct_from:
  some-nonexact-group-has-a-k-inexact-module-triple: that is the open existence of the K-defect; this isolates the single enabling question behind it and identifies the one detector not yet excluded.
  module-defect-needs-non-k-exact-host: that is the established necessary condition on the host (fails Baum--Connes with coefficients); this is the open sufficient-direction crux, once such a host is fixed.
  module-dual-actions-have-no-wandering-open-sets: that excludes the proper-orbit (ghost) detector; this records what detector remains after that exclusion and the tracial one.
---

**OPEN.** Fix an expander-monster host `G` failing Baum--Connes with coefficients
(`osajda-monster-hosts-for-bc-module-route`, items (1),(2),(4)); by
`module-defect-needs-non-k-exact-host` this is forced. The module route
(`bc-counterexample-via-module-k-inexactness`) then turns on:

> **(Q)** Does the Baum--Connes-with-coefficients failure of `G` already occur at a **measured**
> module-dual coefficient `C(V^)` -- one carrying a `G`-invariant probability measure of full
> support -- and in the sub/quotient form of a module triple `(V, W)`?

A "yes" builds a trivial-coefficient counterexample; a proof that measured coefficients always
satisfy Baum--Connes would kill the route.

**Why this is the whole content.**
- The known monster failures are at **boundary** coefficients: `l^inf(G) = C(βG)`, the uniform
  Roe algebra, the coarse-groupoid algebra (Higson--Lafforgue--Skandalis). These carry **no**
  `G`-invariant probability measure -- `βG` has none for infinite `G` -- and the witness is the
  expander's non-compact ghost supported on the boundary.
- A module dual `X = V^` is the opposite: compact metrizable, with the invariant Haar
  probability measure of full support and no proper open orbit
  (`module-dual-actions-have-no-wandering-open-sets`). To our knowledge no counterexample to
  Baum--Connes with coefficients is known at any coefficient with an invariant faithful trace;
  the module route would be the first.

**Detectors, and which survive.**
- *Proper-orbit rank at infinity* (Higson--Lafforgue--Skandalis, Spakula arXiv:0907.2249). Dead
  for module duals: no wandering open set, no proper orbit
  (`module-dual-actions-have-no-wandering-open-sets`).
- *Traces / invariant measures.* Dead as detectors. A trace induced by an invariant measure
  supported on `Z` factors through `q`, so it annihilates `ker q_*` and sees no defect; the
  faithful Haar trace charges the ideal `C_0(U) ⋊_r G` too, so it never certifies a class to lie
  outside the ideal image. Either way an invariant-measure trace cannot separate `ker q_*` from
  `im i_*`.
- *Maximal-versus-reduced comparison.* Not excluded, and the natural home of the defect. The
  maximal crossed product is exact, so
  `0 -> C_0(U) ⋊_max G -> C(X) ⋊_max G -> C(Z) ⋊_max G -> 0` yields a genuine six-term exact
  sequence in K-theory. The reduced defect is the failure of the comparison maps
  `lambda_* : K_*((-) ⋊_max G) -> K_*((-) ⋊_r G)` to carry that exactness down. Equivalently, the
  defect is a Kazhdan-type class: an element of `K_0(C(X) ⋊_max G)` whose reduced image lies in
  `ker q_*^r` but not in `im i_*^r`.

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
- **Residually finite handle, untested.** For an RF host (`osajda-monster-hosts-for-bc-module-route`
  item (4)) with congruence quotients `G/N_i`, the reduced trace of a gapped spectral projection
  is a limit of finite eigenvalue fractions (the mechanism recorded in
  `bc-kun-thom-gap-label-is-congruence-eigenvalue-limit` for the group algebra). Whether the
  analogous congruence approximation computes the **max-vs-reduced** comparison for the module
  coefficient `C((Z/p)^G)`, rather than a trace, is unexplored and is the most concrete next
  probe.
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
