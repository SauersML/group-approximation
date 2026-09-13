---
rg: 2
id: zaremsky-1-20-uncountably-many-simple-fp2-groups
kind: claim
title: "Zaremsky Problem 1.20 resolved: are there uncountably many simple groups of type FP_2, and of type FP?"
root: true
distinct_from:
  uncountably-many-simple-groups-of-type-fp2: that claim is one answer to the first part; this is the two-part question, established only when both parts are answered
  uncountably-many-simple-groups-of-type-fp: that claim is one answer to the second part; this is the two-part question, established only when both parts are answered
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 20,
verbatim: "(Added 6/12/25) Are there uncountably many simple groups of type
FP2? Of type FP?"

This claim is the question. It is established only through an answer route:

- **Yes to both**: `zaremsky-1-20-by-yes` requires
  `uncountably-many-simple-groups-of-type-fp`. Type FP implies type FP_2, so
  this answers the first part too.
- **Yes, then no**: `zaremsky-1-20-by-mixed` requires
  `uncountably-many-simple-groups-of-type-fp2` and
  `only-countably-many-simple-groups-of-type-fp`.
- **No to both**: `zaremsky-1-20-by-no` requires
  `only-countably-many-simple-groups-of-type-fp2`. A countable bound for type
  FP_2 bounds type FP.

Never write a `requires: []` route into this claim.

**Reading.** Groups are counted up to isomorphism. "Simple" means nontrivial
with no normal subgroups other than `1` and the group. Type FP_2 and type FP
are over `Z` (Llosa Isenrich–Schesler–Wu write FP_2(Z)). `G` is of type FP_2
when the trivial module `Z` has a projective resolution over `ZG` that is
finitely generated in degrees at most 2, and of type FP when it has a
finite-length resolution by finitely generated projective modules. Type FP
implies finite cohomological dimension, so a simple group of type FP is
torsion-free. There are only countably many finitely presented groups, so a
"yes" needs, for all but countably many of its members, simple groups of type
FP_2 that are not finitely presented.

**Known context (checked 2026-09-13).**

- Leary, arXiv:1512.06609v4 (Proc. London Math. Soc. 2018), Theorems 1.2 and
  1.3: for a finite connected flag complex `L` that is not simply connected,
  the groups `G_L(S)`, `S ⊆ Z`, realize `2^aleph_0` isomorphism types; when `L`
  and its universal cover are acyclic, every `G_L(S)` is of type FP. None of
  them is simple: each surjects onto `G_L(Z) = BB_L`, an infinite residually
  finite group.
- Llosa Isenrich–Schesler–Wu, arXiv:2510.01952v1 (October 2025), Theorems 1.1
  and 1.4: simple groups, obtained as commutator subgroups of
  Röver–Nekrashevych groups, with the homological finiteness properties of a
  Bestvina–Brady group or of a finitely generated subgroup of `GL_n(Q)`. This
  gives simple groups of type FP_∞ that are not finitely presented. Their
  inputs are countable, so the family is countable, and the groups contain
  finite subgroups, so none is of type FP. Their Question 1.12 is Zaremsky's
  Problem 1.25.
- No simple group of type FP that is not finitely presented was found in the
  sources checked.
- Search bound: web search, arXiv listing searches for "simple groups of type
  FP" and for "almost finitely presented" with "simple" (no results), and the
  two papers above. MathSciNet and zbMATH were not reached.

The lane's tools and firewalls are recorded on the answer claims and in
`research/artifacts/zp-simple-fp2-status-and-reformulation-2026-09-13.md`.

## Attempts

- 2026-09-13 (lane z1-20-simple-fp2): open-status check above. The FP_2 part
  is reformulated as a property of a single finitely presented group, and
  finite-data self-similar constructions are shown to give only countably many
  groups; details on `uncountably-many-simple-groups-of-type-fp2`.
