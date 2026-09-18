---
rg: 2
id: automorphic-sofic-kazhdan-kernel-with-full-mf-radical
kind: claim
title: Some finitely generated torsion-free sofic Kazhdan group with full MF radical has an automorphism with a finite two-sided automorphic presentation
distinct_from:
  torsion-free-sofic-singly-generated-kazhdan-defect-core: that asks for a finitely presented full-radical core produced by a compression defect, which crosses Alekseev--Thom 6.1; this asks for a possibly infinitely presented kernel whose full radical may come from any mechanism, with the finiteness supplied by an automorphic presentation.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that asks for a kernel which may be MF and is saturated by an extrinsic defect of the mapping torus; this asks for a kernel with full MF radical in isolation, so the automorphism only supplies finite presentation.
  fp-sofic-kazhdan-group-not-residually-finite: that is Alekseev--Thom 6.1; a finitely presented instance of this claim answers it, but the claim is designed for infinitely presented kernels, which do not.
  mf-kazhdan-quotientless-mapping-torus-exact-radical: that is the extrinsic half (IO-ext) of the descent, with an MF kernel; this is the intrinsic half (IO-int), with a kernel that has no nontrivial MF quotient.
artifacts:
  - research/finite-outer-order-radical-witnesses-cross-alekseev-thom.md
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
---

**OPEN.** There exist a finitely generated group `K` and `phi in Aut(K)` such that

```text
(P1) K is nontrivial, torsion-free, sofic and Kazhdan, and Rad_MF(K) = K;
(P2) K has a finite two-sided automorphic presentation (FAP1) for phi.
```

`exact-mf-radical-over-z-via-automorphic-full-radical-kernel` turns any such pair into a witness
of `torsion-free-sofic-exact-mf-radical-over-z`.

**Why this is the right branch.** By `finite-outer-order-radical-witnesses-cross-alekseev-thom`,
every witness of the goal either answers Alekseev--Thom 6.1 or lies in region (IO). There the kernel
is infinitely presented and `[phi]` has infinite order in `Out(K)`. Descent splits (IO) into
(IO-ext) and the present (IO-int). Here the radical of the mapping torus is **intrinsic**, so the
compression-defect obstructions do not apply: (IS), (NB), (BF), (GC) and (CI) in the extrinsic-kernel
node's Attempts 16 to 19 all concern defects created by the mapping torus. The price is (P1).

**Forced features.**
- If `K` in a solution is infinitely presented, as intended, then `[phi]` has infinite order in
  `Out(K)`. Otherwise a finite-index subgroup `K x Z` of the finitely presented mapping torus would
  make `K` finitely presented.
- `K` has no nontrivial finite quotient, since finite groups are MF. In particular `K` is not
  residually finite.
- `K` is not LEF. A LEF group is operator MF by `lef-implies-operator-mf`, so a LEF `K` would
  have `Rad_MF(K) = 1`, not `K`.
- `K` is not MF, for the same reason.

**Independent failure points.**
- (P1) alone is open and is not recorded anywhere in the graph. It asks for a finitely generated
  sofic Kazhdan group with no nontrivial MF quotient. The known Kazhdan full-radical groups have
  the wrong profile:
  - `defect-saturation-full-mf-radical`: soficity unknown;
  - `eighteen-relator-kazhdan-group-with-full-mf-radical`: not sofic;
  - Titz--Witzel residuals: both soficity and non-MF unknown.

  Known sofic Kazhdan groups without finite quotients, such as
  `simple-kazhdan-lef-group-from-minimal-subshift`, are LEF and hence MF. A **refutation** of (P1),
  that every sofic Kazhdan group has a nontrivial MF quotient, would kill this branch and the whole
  finite-outer-order region at once. It would also answer Alekseev--Thom 6.1 negatively in the
  strong form "every finitely presented sofic Kazhdan group has a nontrivial MF quotient".
- (P2), given a (P1) group, is a finiteness question about one automorphism. Hull--Osin style
  limits `R / union N_k` are natural (P1) candidates. There (P2) asks the normal subgroups `N_k` to
  be the orbit of finitely many relators under one automorphism of the free group, rather than an
  arbitrary increasing union.

## Attempts
