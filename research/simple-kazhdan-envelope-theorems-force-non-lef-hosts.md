---
rg: 2
id: simple-kazhdan-envelope-theorems-force-non-lef-hosts
kind: claim
title: For sofic, hyperlinear, weakly sofic, linear sofic, initially subamenable and operator-MF groups, a simple Kazhdan envelope theorem forces a non-LEF simple Kazhdan host
distinct_from:
  sofic-universal-envelope-forces-non-lef-simple-kazhdan: that is the sofic case with the non-amenable witness BS(2,3); this treats every subgroup-closed class containing the finitely presented amenable Abels–Prüfer quotient, so it also covers hyperlinear, initially subamenable and operator-MF groups.
  approximation-classes-without-simple-kazhdan-members: that lists classes with no simple Kazhdan members at all; this is about classes that contain the LEF hosts and are strictly larger than LEF.
---

**ESTABLISHED (unreviewed).**
- **Hypothesis.** Let `P` be a class of countable groups closed under subgroups and containing the finitely presented
  amenable Abels–Prüfer quotient `Γ_p` for some prime `p` (`abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`).
- **Claim.** If every finitely generated group in `P` is a subgroup of an infinite finitely generated simple Kazhdan
  group in `P`, then some infinite finitely generated simple Kazhdan group in `P` is not LEF. That group contains
  `Γ_p`, a finitely presented solvable group that is not residually finite.
- **Covered classes.** `P` can be any of: sofic groups; hyperlinear groups; weakly sofic groups; linear sofic groups over
  any field; initially subamenable groups; operator-MF groups (`amenable-implies-operator-mf`). Each contains every
  countable amenable group.

**Meaning.** LEF is the only standard approximation class larger than the residually finite groups for which the
envelope theorem is known (`lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple`). For each class above, the
envelope theorem is at least as hard as producing one infinite simple Kazhdan group in that class that is not LEF.
Every simple Kazhdan sofic, hyperlinear or operator-MF group on this graph whose approximation property is proved is
LEF. The one exception is linear soficity over finite fields: `simple-kazhdan-linear-sofic-non-lef-group-exists`
(established, unreviewed, repaired 2026-09-13) supplies a non-LEF simple Kazhdan group that is linear sofic over a
finite field. So the cost statement does not obstruct that class, although the envelope theorem there is still open.

Route: `simple-kazhdan-envelope-theorems-force-non-lef-hosts-proof`.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part3.md`):** PASS, conditional on the imports `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`, `finitely-presented-lef-groups-are-residually-finite` and `amenable-implies-operator-mf` (§2).
