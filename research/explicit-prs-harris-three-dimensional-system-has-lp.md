---
rg: 2
id: explicit-prs-harris-three-dimensional-system-has-lp
kind: claim
title: An explicit regular-dominating nonamenable completion has an LP Harris generator system
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
distinct_from:
  explicit-proper-d-completion-with-llp-exists: that asks for LLP of the whole proper Brown-Guentner completion; this allows any regular-dominating nonamenable representation and asks only for LP of its explicit three-dimensional Harris system.
  non-rf-kazhdan-group-with-llp-full-c-star-algebra: that targets the full group algebra of a non-RF Kazhdan group; this needs neither the full norm nor a Kazhdan or residual hypothesis.
---

**OPEN CLAIM.**  Give an explicit finitely generated group `G`, an explicit
unitary representation `pi`, and a finite generating tuple such that

```text
lambda_G prec pi,
pi is nonamenable,
the Harris system S_pi=span{I,D,G_H} in M_(n+2)(C^*_pi(G)) has LP. (PH3D1)
```

By `lp-of-harris-generator-system-forces-nonhyperlinear`, the same `G` is
an explicit non-hyperlinear group.

This is a three-dimensional normal form for the positive LLP-family
target, with `D` diagonal and `G_H` a fixed sparse matrix labeled by the
chosen group generators.  By
`lp-of-harris-generator-system-forces-nonhyperlinear`, LP of this special
system implies LLP of the ambient representation completion.  It is
therefore smaller syntactically, but not a logically weaker lifting
requirement.

**CORRECTED 2026-08-23.**  This paragraph previously said LP of the system
is *equivalent* to ambient LLP.  The converse is withdrawn
(`harris-lp-to-llp-implication-is-one-directional`), so the target here is
sufficient and potentially strictly stronger than ambient LLP.  The claim
and its consuming route are unaffected -- both use only the sufficient
direction -- but this node should no longer be preferred to the ambient LLP
targets on the ground that it is the same problem in fewer dimensions.
