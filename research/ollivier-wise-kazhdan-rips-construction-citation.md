---
rg: 2
id: ollivier-wise-kazhdan-rips-construction-citation
kind: route
title: Import Ollivier--Wise Theorem 1.1 and the dimension statement of their Section 2.1
target: ollivier-wise-kazhdan-rips-construction
requires: []
---

Y. Ollivier, D. T. Wise, *Kazhdan groups with infinite outer automorphism group*,
arXiv:math/0409203v1 (13 Sep 2004). Read from the PDF on 2026-09-13.

**Theorem 1.1 (verbatim, pp. 1--2).**

> For each countable group `Q`, there is a short exact sequence `1 -> N -> G -> Q -> 1` such that
> (1) `G` is torsion-free,
> (2) `G` has a graphical `1/6` presentation, and
> (3) `N` has property `T`.
> (4) Moreover, `G` is finitely generated if `Q` is, and finitely presented if `Q` is.

**Section 2.1 (verbatim, p. 3).**

> The condition `Gr'(1/6)` implies that the group `G` is torsion-free, word-hyperbolic, of
> dimension 2, just as the `C'(1/6)` condition [Oll03b].

**How it is used.**
- "Of dimension 2" is read as: the graphical presentation complex is aspherical and
  two-dimensional, as for `C'(1/6)` presentations. Hence `cd G <= 2`.
- Word-hyperbolicity is used only for finite presentations, and none of the consumers needs it.
- The asphericity reading has independent support. D. Gruber, arXiv:1210.0178:
  - Theorem 2.18: the presentation complex of a graphical `C(6)` presentation is aspherical.
  - Corollary 2.19: "`G(Γ)` has an at most 2-dimensional `K(G(Γ),1)` space and hence
    cohomological dimension at most 2".
  - A `Gr'(1/6)` graph is graphical `C(7)`: every piece is shorter than a sixth of each cycle
    containing it. So `cd G <= 2`.
- Gruber's statements were read by `ex-verify2-groups`, not by this lane. That lane also checked
  Theorem 1.1 (1)–(4) verbatim, with PASS. Review: e106d0ae75,
  `research/artifacts/ex-review2-groups-2026-09-13-part4.md` §1. [Oll03b] itself was not re-read.
