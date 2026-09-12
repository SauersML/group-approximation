---
rg: 2
id: permanence-closure-contains-fg-simple-nonsofic-group
kind: claim
title: Some infinite finitely generated simple nonsofic group lies in the surjunctivity permanence closure
root: true
distinct_from:
  finitely-generated-simple-groups-are-surjunctive: that is the universal reduction of Gottschalk's conjecture; this asks for one simple nonsofic group that the landed permanence methods already make surjunctive.
  gottschalk-counterexamples-lie-outside-the-permanence-closure: that excludes finitely presented simple nonsofic groups from S*; this asks whether any finitely generated, necessarily infinitely presented, simple nonsofic group lies in S*.
  fg-simple-subgroups-of-local-embedding-free-closure-are-sofic: that proves the O3-free closure contains no such group; this asks whether local embeddings supply one.
artifacts:
  - research/artifacts/fg-simple-groups-and-the-permanence-closure-2026-09-12.md
---

**OPEN.** There is an infinite, finitely generated, simple, nonsofic group `Q` in the
closure `S*` of `gottschalk-counterexamples-lie-outside-the-permanence-closure`.

**Why it matters.**
- Every group of `S*` is surjunctive, so `Q` would be the first simple nonsofic group
  known to be surjunctive: a positive case of Gottschalk's conjecture on a simple
  nonsofic host, in the class to which the conjecture reduces.
- By `fg-simple-subgroups-of-local-embedding-free-closure-are-sofic`, `Q` must enter
  through local embeddings and cannot be finitely presented. The target is therefore
  an infinitely presented simple nonsofic group every finite ball of which embeds as a
  partial multiplication table into a group of `S*`.

*Marked `root` because it asks a top-level question in its own right, like
`surjunctive-nonsofic-group-exists`.*

## Attempts

- **Unions, folds and extensions.** They are dead by the O3-free theorem. A simple
  amalgam or HNN extension folding faithfully on vertex groups into a surjunctive `G`
  embeds into `G`, since the fold kernel is free. A directed union containing a
  finitely generated simple `Q` already contains it at a finite stage.
- **Simple subgroups of known witnesses.** Kun–Thom wreaths, doubles and graph wreaths
  have sofic kernels over residually finite or sofic bases, so every finitely generated
  simple subgroup is sofic. Nothing to extract.
- **Marked limits of wreaths with growing finite simple lamps.** `Alt(k_n) wr_(G/Gamma) G`
  lies in `S*` and contains the Kun–Thom wreath. As `k_n` grows, the limit is a wreath
  with LEF lamps: surjunctive and nonsofic, but the lamp subgroup stays normal. A
  simple limit needs base generators to become short products of lamp commutators in
  the limit. No design is known yet.
- **Concrete candidate: an alternating full group.** Let `W = (Z/2) wr_(G/Gamma) G` be the
  Kun–Thom wreath, acting on the Cantor set `X = {0,1}^(G/Gamma)` by flips and site
  permutations, and let `Q = A(W ↷ X)` be Nekrashevych's alternating full group of this
  action. The imported statements below were not re-read from source, and no node
  depends on them.
  - *Simple and finitely generated.* The action is minimal, since `W` flips any finite
    set of coordinates and `G` is transitive on sites. It is expansive, since
    cylinders at one site and their `W`-translates separate points. Nekrashevych
    (Simple groups of dynamical origin, 2019) gives simplicity for minimal effective
    actions and finite generation for expansive ones.
  - *Nonsofic, conditionally.* If `A(W ↷ X) = [[W ↷ X]]'`, then `Q` contains `[W,W]`.
    `G` is perfect for `r, d >= 3`, so `[W,W]` is the even-lamp subgroup extended by `G`.
    It has index 2 in `W` and is therefore nonsofic.
  - *Open step.* Every finite ball of `Q` must embed as a partial table into a group of
    `S*`. Elements of `Q` are piecewise `W`-translations controlled by cylinders on
    finitely many sites. The natural targets are permutational wreath products over the
    Kun–Thom base with finite lamps on the controlling sites, as in the marked-site
    peeling of `rf-lamp-wreath-surjunctivity-by-marked-site-peeling`. No such embedding
    has been built yet.
- **Also not tried.** Small cancellation embeddings of a Kun–Thom wreath into infinitely
  presented simple groups. Quotients are involved, so balls must be checked directly.
- **Corrected candidate (w4-simple-q, artifact
  `research/artifacts/kun-thom-alternating-full-group-2026-09-12.md`).**
  - *On lamp configurations alone.* `A(W ↷ {0,1}^(G/Gamma))` contains `N semidirect EL_r(R)`,
    through rigid-stabilizer commutators and because `EL_r(R_+)` is perfect. Containing `[W,W]`
    is equivalent to containing `SL_d(Z)`. An element whose `SL_d(Z)` image has infinite order
    preserves no proper clopen set, so fragmentation stops there, and the conditional above
    stays open.
  - *Adding a finite quotient `G/K`, `|G/K| >= 3`.* This removes the question: the alternating
    full group of `{0,1}^(G/Gamma) x G/K` contains `N semidirect [K,K]`, which has finite index
    in the image of `W`, so it is nonsofic (`kun-thom-product-action-alternating-full-group-is-nonsofic`).
  - *Open nodes.* Simplicity and finite generation are
    `kun-thom-product-action-alternating-full-group-is-fg-simple`, which rests on Nekrashevych's
    theorems, not re-read. The local-embedding step is
    `kun-thom-full-group-balls-embed-in-permanence-closure`. Route:
    `permanence-closure-fg-simple-nonsofic-via-kun-thom-full-group`.
  - *Where the natural hosts die.* O4 wreaths with a marked-site assignment fail at overlapping
    windows. `H_fin semidirect G` misses varying base parts, and `S*` cannot reach it because
    `H_fin` is simple. Layered wreaths vary base parts only along layers.
