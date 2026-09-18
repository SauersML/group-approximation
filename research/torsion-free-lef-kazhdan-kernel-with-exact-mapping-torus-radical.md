---
rg: 2
id: torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical
kind: claim
title: Some torsion-free LEF Kazhdan group has a finitely presented mapping torus whose MF radical is the whole kernel
distinct_from:
  mf-kazhdan-quotientless-mapping-torus-exact-radical: that is (XMF) for an arbitrary MF kernel, with no torsion-freeness, LEF or finite presentation; this is its torsion-free, LEF, finitely presented specialization, which alone is equivalent to the flagship witnesses lying in the permanence closure.
  exact-kazhdan-radical-kernel-cannot-be-lef: that states (EKL1); this asserts a torsion-free, finitely presented counterexample to it.
  lef-kazhdan-group-without-finite-quotients-exists: that group is LEF, Kazhdan and quotientless but torsion-generated; this needs a torsion-free kernel and an automorphism with exact radical.
  torsion-free-lef-kazhdan-non-rf-seed: that seed is torsion-free, LEF and Kazhdan but has finite quotients, so its mapping-torus radicals stay inside its centre.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that asks for a sofic kernel with an extrinsic compression defect; this asks for a LEF kernel and a bare radical equation, with soficity automatic.
artifacts:
  - research/permanence-closure-radical-witnesses-have-lef-kernels.md
---

**OPEN.** There exist a nontrivial finitely generated group `K` and `φ ∈ Aut(K)` such that

```text
(LK1)  K is torsion-free, LEF and has property (T);
(LK2)  G = K ⋊_φ Z is finitely presented;
(LK3)  Rad_MF(G) = K × {0}.
```

**Why it matters.** By `permanence-closure-radical-witnesses-have-lef-kernels`, this claim is
exactly the part of `torsion-free-sofic-exact-mf-radical-over-z` whose witnesses lie in the sofic
permanence closure. Here soficity comes for free, and the route
`torsion-free-sofic-exact-mf-radical-via-lef-kernel` closes the flagship from this claim alone. Every
other witness needs a non-LEF sofic Kazhdan kernel certified outside the permanence closure.

**Forced structure** (from the established claim). Any solution has these properties:
- `K` is MF with `Rad_MF(K) = 1`;
- `K` has no nontrivial finite quotient and is not finitely presented;
- `[φ]` has infinite order in `Out(K)`;
- `G` is sofic, non-MF, and not LEF.

**Prerequisites, each of which can fail on its own.**
- **(L1)** A torsion-free LEF Kazhdan group without nontrivial finite quotients exists. This is unknown.
  - `lef-kazhdan-group-without-finite-quotients-exists` fails torsion-freeness, and so does every
    elementary group `EL_n(R)` with `n ≥ 3`, by `steinberg-images-die-in-torsion-free-groups`.
  - `torsion-free-lef-kazhdan-non-rf-seed` fails quotientlessness.
  - The live programs are these:
    - the torsion-free alternating-mother limits of `torsion-free-kazhdan-alternating-mother-limit-gate`;
    - the relation-module covers of `kazhdan-rational-relation-cover-reduction`, provided the cover
      stays LEF.
- **(L2)** (EKL1) fails for that kernel. Any argument for (EKL1) would kill this claim outright. The
  periodization attempt of `mf-kazhdan-quotientless-mapping-torus-exact-radical` (Attempt 1) records why
  the obvious MF-construction for `G` dies at the wrap. So (L2) is not known to fail.
- **(L3)** A finite automorphic presentation of a kernel which is itself not finitely presented. See
  `fp-mapping-torus-iff-finite-automorphic-presentation`.

**Finite-model reading of (LK3).** `K` is a marked limit of finite groups `F_n`. These are uniformly
Kazhdan, since they eventually become quotients of one finitely presented Kazhdan cover. (LK3) says no
sequence of almost-representations of `G` in the norm corona can be faithful on `K`. A natural first test
case is (L1)-(L2) for a torsion-free alternating limit with `φ` induced by an automorphism of the mother
group that permutes the quotient sequence.
