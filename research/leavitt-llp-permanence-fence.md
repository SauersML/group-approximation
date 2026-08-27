---
rg: 2
id: leavitt-llp-permanence-fence
kind: claim
title: Every standard group-theoretic LLP permanence route is circular for the binary Leavitt unit group
distinct_from:
  non-rf-kazhdan-group-with-llp-full-c-star-algebra: That is the open existence target whose positive resolution would produce a non-hyperlinear group; this is a negative structural audit of the currently published permanence mechanisms at one explicit candidate, and it does not decide its LLP.
  llp-non-rf-kazhdan-group-is-non-hyperlinear: That theorem explains why LLP of the Leavitt group would prove non-hyperlinearity; this theorem explains why the usual constructions cannot establish that LLP without already containing the same hard case.
  no-published-unconditional-codense-stable-host: That audits flexible Hilbert--Schmidt stability hosts; this audits local-lifting permanence for the binary Leavitt unit group and includes the independent F2-times-F2 subgroup fence.
  leavitt-steinberg-hs-stability-fork: That is a normalized-Hilbert--Schmidt stability dichotomy for a Steinberg cover; this is about Kirchberg LLP of the full C-star algebra of the unit group itself.
artifacts:
  - research/artifacts/leavitt-llp-permanence-audit-2026-08-21.md
  - GroupApproximation/Leavitt/ThompsonVEmbedding.lean
---

Let

```text
R = L_(F_2)(1,2),             G = R^x.
```

The positive group permanence theorems for the local lifting property in
Fournier-Facio--Willett, arXiv:2603.18456v2, Section 3, do not reduce LLP of
`C^*(G)` to proper simpler pieces:

1. a directed-union proof has a stage equal to `G`;
2. an amenable-extension proof has kernel equal to `G`;
3. a finite-edge graph-of-groups proof has a vertex group equal to `G` after
   reduction.

Moreover, subgroup inheritance gives a separate hard lower bound:

```text
C^*(G) has LLP  ==>  C^*(F_2 x F_2) has LLP.             (LLPF)
```

The conclusion on the right of `(LLPF)` is Question 1.6 of the same 2026
paper and remains open there.  Thus the Leavitt self-similarity, its finite
prefix groups, and its Thompson subgroup do not put `G` inside any currently
known LLP permanence class.  This is a fence, not a proof that `C^*(G)` fails
LLP: a genuinely new positive theorem for this property-(T) group would still
prove the program's main goal by
`llp-non-rf-kazhdan-group-is-non-hyperlinear`.

