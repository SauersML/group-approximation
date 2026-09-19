---
rg: 2
id: dual-surjunctive-groups-are-surjunctive
kind: claim
title: Every dual surjunctive group is surjunctive
distinct_from:
  surjunctive-groups-are-dual-surjunctive: that is the converse implication between the two properties.
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

**OPEN.** If every post-surjective automaton over `G` (every finite alphabet)
is pre-injective, then every injective automaton over `G` is surjective.

Both properties hold for sofic groups. Both imply Kaplansky's direct
finiteness over fields of positive characteristic: Doucha–Gismatullin for the
dual property, and the standard linear argument for surjunctivity.

**Route.** `dual-surjunctive-surjunctive-via-post-surjective-decoders` derives
this from `strict-pairs-admit-post-surjective-decoders` together with
`post-surjective-decoders-convert-strict-pairs-to-dual-failures`.

## Attempts

- **2026-09-18, swarm-0917-w14-w14-gs-break [host-geometry]: host change. DEAD. The claim stays OPEN.**
  - **Plan.** Turn a strict pair at `G` into a dual failure on a full shift by changing the host. Use layered
    decoders over `G × Z`, or decoders that read neighbours through a free-product factor, so that the defect
    sites of `σ` get new room to absorb lifts.
  - **Where it dies.** Every layer that absorbs the defects of the layer below creates its own defects, and the
    cascade never terminates. Cutting it off at a finite layer is the same as extending `σ|_{X_R}` from the
    bounded-defect domain `X_R` to the full shift with post-surjectivity kept. Equivalently, it is a
    post-surjective cover of `X_R` by a full shift. That is the original problem
    (`strict-pairs-admit-post-surjective-decoders`), so the host change buys nothing. Also, the new host is not
    `G`, and dual surjunctivity of `G × Z` or `G * Z` is not implied by that of `G`.
  - **By-product (ESTABLISHED, elementary).** `alphabet-enlarging-covers-refute-dual-and-domain-duality`. A
    strongly post-surjective automaton `A^G → B^G` with `|B| > |A|` refutes dual surjunctivity, CP and PSD at
    `G`. It misses a constant, so it and every failure derived from it have no right inverse. New OPEN claim
    `post-surjective-automata-never-enlarge-the-alphabet` (NPE). It holds for linear maps over every group, by
    augmentation, fails for the free monoid, and is implied by dual surjunctivity. So the hypothesis of this
    claim includes a rank-type core that strict pairs never touch: the route here only ever uses dual
    failures that have a right inverse, and NPE failures have none.
