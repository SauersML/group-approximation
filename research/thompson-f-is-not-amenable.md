---
rg: 2
id: thompson-f-is-not-amenable
kind: claim
title: Thompson's group F is not amenable
root: true
distinct_from:
  thompson-f-is-amenable: that is the amenable answer to the same named problem; this is the non-amenable answer, which would make F a finitely presented non-amenable group without free subgroups.
---

**OPEN.** Richard Thompson's group `F` is not amenable.

*Marked `root` because it answers a named open problem.* A proof would give a
finitely presented, torsion-free, left-orderable non-amenable group with no free
subgroups (`thompson-f-has-no-free-subgroups`). Survey: V. Guba,
arXiv:2305.07113v4 (2023). The opposite root is `thompson-f-is-amenable`. Source
map: `research/artifacts/thompson-f-amenability-map-2026-09-12.md`.

## Attempts

- **Free subgroups.** Excluded by `thompson-f-has-no-free-subgroups`. A proof
  needs a mechanism other than a free subgroup: a paradoxical decomposition
  without free groups, a uniform isoperimetric inequality, or a non-Ore pair in
  `K[F]`. Dies: no such mechanism is known for `F`.
- **Spectral gaps from property (T).** Excluded: `F` lies in `V`, which has the
  Haagerup property (`thompson-v-has-haagerup-property`), so every Kazhdan
  subgroup of `F` is finite and no Kazhdan-type uniform gap is available. The
  Haagerup property does not obstruct non-amenability either, since free groups
  have it.
- **Numerical cogrowth.** Cogrowth sampling for the standard generators
  (Elder–Rechnitzer–Janse van Rensburg, *Random sampling of trivial words in
  finitely presented groups*, Exp. Math. 24 (2015), arXiv:1312.5722;
  Haagerup–Haagerup–Ramirez-Solano, Int. J. Algebra Comput. 25 (2015)) is
  reported to point toward non-amenability. Elder–Rogers, arXiv:1608.06703,
  "identify two potential sources of error" in that method (abstract). Dies:
  finite data cannot certify an asymptotic growth rate, and this graph has read
  none of the numerical values.
- **Non-Ore certificate.** By `thompson-f-amenable-iff-group-ring-is-ore`,
  non-amenability is equivalent to a pair `a, b` in `K[F]` with no nonzero common
  multiple. A finite search can propose candidate pairs, but ruling out every
  multiple needs a structural invariant. Dies: none is known.
- **Unaccepted claims.** arXiv:1408.2188 claims non-amenability, and Shavgulidze's
  papers claim amenability (critiqued in arXiv:1102.0747). Neither is an accepted
  result. They are recorded so that no lane cites them as theorems.
