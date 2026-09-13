---
rg: 2
id: punctured-surface-mcgs-virtually-embed-in-aut-free-groups
kind: claim
title: Extended mapping class groups of finite-type surfaces with a puncture or boundary have a finite-index subgroup embedding in some Aut(F_n)
distinct_from:
  punctured-surface-mcgs-satisfy-permutational-boone-higman: that imports the permutational Boone--Higman property of these groups; this imports only the embedding steps of the same proof, a finite-index subgroup inside an automorphism group of a free group, which is what Zaremsky Problem 3.10 needs.
  closed-mcgs-virtually-embed-in-punctured-mcgs: that is the open premise for closed surfaces of genus at least three; this is the known case of surfaces that already have a puncture or boundary.
---

**ESTABLISHED (literature import).** The derivation is
`punctured-surface-mcgs-aut-embedding-citation`.

Let `Σ` be an orientable surface of finite type with at least one puncture or
nonempty boundary, and `MCG^±(Σ)` its extended mapping class group. Then some
finite-index subgroup of `MCG^±(Σ)` embeds in some `Aut(F_n)`.

By item 2 of `aut-free-embeddability-passes-to-finite-index-overgroups`,
`MCG^±(Σ)` itself then embeds in some `Aut(F_n)` (no route records this
corollary separately).

**Scope.** Boundary conventions: the capping step below handles mapping classes
fixing the boundary; for the convention where the boundary is only preserved
setwise, the group is the mapping class group of the punctured surface obtained by
collapsing each boundary component, which is covered by the puncture cases.
Surfaces with finite or virtually cyclic mapping class groups are trivially covered
(a trivial or infinite cyclic finite-index subgroup embeds in `Aut(F_2)`).
