---
rg: 2
id: bcs-to-lcs-exact-support-gap
kind: claim
title: A tracial non-RU BCS admits an exact robust LCS sub-menu with approximate soundness
distinct_from:
  robust-locally-satisfiable-relator-code: that asks for sparse group-ball preservation with no ambient tracial witness; this target uses a tracial BCS witness to certify nontriviality of the central mark and asks for an exact LCS sub-menu that rejects every marked approximate profile.
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
  - notes/FALSE_PERFECT_COMPLETENESS_MASK_NO_GO.md
---

Starting from a finite BCS `B` which is tracially satisfiable but not
`R^U`-satisfiable, construct a finite **linear-system / LCS** relator menu `S`,
a distribution `mu` on `S`, a marked central involution `J`, and a tracial
unitary assignment `rho` such that, for some

```text
0 < eps < eps_plus,
delta > 0,
```

the following strict inequality holds.

Let

```text
E = {r in S : rho(r)=1 exactly},
g = mu(E).
```

Among all finite-dimensional unitary assignments with
`d_2(J,1)>=delta`, let `q` be the supremum `mu`-mass of relators whose defect
is at most `eps_plus`. Then

```text
g > q.
```

By `exact-support-gap-nonexact-checks-no-advantage`, this condition is
qualitatively equivalent to the following simpler target: **every marked
finite-dimensional profile rejects at least one relator in the exact support
`E`**. Since `E` is finite, uniform measure on `E` then has exact tracial
completeness and a rejection margin at least `1/|E|`. Nonexact checks in
`S\E` cannot create the gap and may be discarded for existence purposes.

Thus this node should be read as an exact-robust-sub-menu compiler target, not
as a weaker route around perfect completeness. `exact-support-relator-sparsification`
remains useful downstream for finite-moment extraction once such an exact
sub-menu has been found.

## Attempts

- **Published Taller--Vidick test, unmodified.** Their completeness loss comes
  from the noisy mask. The relevant question is now whether the subfamily of
  checks that are operator-exact for the tracial strategy is itself sound
  against every marked finite-dimensional approximate assignment. The
  published unconditioned soundness theorem does not imply this conditioned
  statement.
- **Mask reweighting alone cannot help.** The no-advantage lemma shows that
  putting weight on checks outside `E` cannot improve the qualitative target.
  Any successful reweighting must ultimately expose a robust exact subset of
  `E`; the finite zero-sum formulation in `exact-menu-gap-is-zero-sum-game`
  can optimize its quantitative margin.
- **Quantum-sound gadget compiler.** Seek a source-specific reduction from the
  known tracial/non-`R^U` BCS to LCS checks whose exact-support subfamily
  preserves approximate-model soundness. This is compatible with the
  predicated-control route: `controlled-linear-predication-normal-form` removes
  controlled equations exactly, leaving selector soundness as a finite
  compiler invariant.
- **Modern repetition/PCP amplification.** Amplification is useful only if it
  also preserves or exposes an exact-support family whose conditioned value is
  below one. Driving the unconditioned value down while the exact subfamily
  remains perfectly satisfiable by a bad profile does not move this target.
