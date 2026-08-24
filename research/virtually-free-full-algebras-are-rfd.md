---
rg: 2
id: virtually-free-full-algebras-are-rfd
kind: claim
title: The full C-star algebra of a finitely generated virtually free group is residually finite dimensional
artifacts:
  - research/artifacts/enders-shulman-ffw-llp-sources-2026-08-21.md
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
distinct_from:
  triangle-colimit-llp-reduces-to-relator-local-splitting: that records that `C^*(G_0)` has the lifting property, an approximation property of ucp maps into quotients; this records that its finite-dimensional representations are jointly faithful, which neither implies nor is implied by the LP.
  llp-non-rf-kazhdan-group-is-non-hyperlinear: that is about residual finiteness of a Kazhdan group and hyperlinearity; this is about joint faithfulness of finite-dimensional representations of a virtually free group's full algebra, with no Kazhdan, hyperlinearity or non-residual-finiteness content.
---

**ESTABLISHED (literature import, credited).**  Let `G` be a finitely
generated virtually free group.  Then the finite-dimensional representations
of `G` are jointly faithful on `C^*(G)`:

```text
||a||_(C^*(G)) = sup { ||rho(a)|| : rho finite-dimensional },
                                    a in C^*(G).             (VFR1)
```

Equivalently `C^*(G)` is RFD.  In particular this applies to
`G_0 = P_12 *_(P_2) P_23` of
`triangle-colimit-llp-reduces-to-relator-local-splitting`, which that node
proves is finitely generated virtually free.

Import: `virtually-free-full-algebras-are-rfd-citation`.

**Credit and exact provenance.**  Free groups have Lubotzky--Shalom's property
FD -- the representations with finite image are dense in the unitary dual
(Lubotzky--Shalom, *Finite representations in the unitary dual and Ramanujan
groups*).  Property FD passes from a finite-index subgroup to the ambient group
by inducing representations, so a finitely generated virtually free group has
FD.  Density of finite-image representations in the unitary dual makes the
universal representation weakly contained in the finite-dimensional ones, which
is `(VFR1)`.  Fournier-Facio--Willett, arXiv:2603.18456, is the current
reference that packages LP together with property FD for the surrounding
classes; its Theorem 1.2 and Corollary 4.1 are source-verified in
`research/artifacts/enders-shulman-ffw-llp-sources-2026-08-21.md`.

**Verification status, stated rather than assumed.**  The Fournier-Facio--
Willett statements were read at source on 2026-08-21.  The Lubotzky--Shalom
property-FD theorem and its finite-index permanence are cited here at
statement level and were **not** re-read at source on 2026-08-23; the same
holds for the amalgamated-free-product route (`C^*(G_0)` is a full amalgamated
free product of finite-dimensional algebras over a finite-dimensional
subalgebra, a shape for which RFD permanence is recorded in the operator
algebra literature), which is listed only as an independent confirmation to
check, not as a second proof.  Any consumer that needs `(VFR1)` unconditionally
must close one of these two readings first; consumers are expected to carry
this node as a named requirement rather than absorb it into their own proofs,
which is why it is a separate claim.  Its only consumer is
`local-ucp-sections-from-finite-relator-reservoir`.
