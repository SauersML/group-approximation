---
rg: 2
id: nonhyperlinear-from-proper-d-completion-llp
kind: route
title: Use LLP of one proper Brown-Guentner completion to obtain a non-hyperlinear group
target: non-hyperlinear-group
requires:
  - explicit-proper-d-completion-with-llp-exists
  - llp-regular-dominating-completion-forces-nonhyperlinear
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
---

Take the explicit pair `(G,D)` from
`explicit-proper-d-completion-with-llp-exists`.  Since `G` is nonamenable,
`D` contains `c_00(G)`, and `C^*_D(G)` is a proper canonical quotient of
`C^*(G)`, Paulsen--Rahaman--Samei Theorem 4.9 says that `C^*_D(G)` has no
amenable trace and that hyperlinearity of `G` would force failure of LLP.
But the open claim gives LLP.  Hence `G` is not hyperlinear.

No central extension, stability theorem, finite-dimensional residual
kernel, or full-completion LLP is used.  The witness is `G` itself.
