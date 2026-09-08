---
rg: 2
id: cornulier-kazhdan-groups-are-central-quotients-of-linear-groups
kind: claim
title: The finitely presented non-Hopfian Kazhdan groups are central quotients of linear groups
distinct_from:
  cornulier-non-hopfian-kazhdan-groups-are-mf: that is the analytic conclusion drawn from this structure; this is only the structural identification imported from the literature, with no approximation statement in it.
  affine-congruence-source-is-kazhdan: that is a level-three affine congruence group used as a compression source, with a proper self-embedding of its translation factor; this is a different published family, non-Hopfian and finitely presented, and is imported rather than constructed.
  defect-forces-proper-self-embedding: that is the structural demand for a core that embeds properly in itself; this identifies the standard published family satisfying that demand, so that it can be tested.
artifacts:
  - research/artifacts/central-quotient-rf-exclusion-2026-09-08.md
---

**ESTABLISHED BY PRIMARY SOURCE.**  The finitely presented non-Hopfian
groups with property (T) and infinite outer automorphism group of
Cornulier's Definition 2.4 have the form

```text
Gamma / Z,     Gamma <= GL_r(Z[1/p]),     Z <= Z(Gamma),          (CN1)
```
for a prime `p`.  Property (T) and non-Hopficity are his Proposition 2.7;
finite presentability is his Theorem 1.3.

Moreover such a `Gamma` is **residually finite**: for `A != I` in
`GL_r(Z[1/p])`, pick a nonzero entry of `A - I` and a prime different from
`p` not dividing its numerator; reduction modulo that prime is defined on
`Z[1/p]` and separates `A` in a finite general linear group.

Only the structural identification `(CN1)` is imported.  Nothing about
outer automorphism groups, the erratum, or the proofs of property (T) and
non-Hopficity is used downstream.

DERIVATION
cornulier-kazhdan-central-quotient-citation
