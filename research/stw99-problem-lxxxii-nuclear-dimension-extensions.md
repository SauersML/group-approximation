---
rg: 2
id: stw99-problem-lxxxii-nuclear-dimension-extensions
kind: claim
title: Nuclear dimension should be the maximum across an extension (STW Problem LXXXII)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw82-one-color-gluing-audit-2026-08-30.md
---

**Problem LXXXII of Schafhauser--Tikuisis--White,
[arXiv:2506.10902v2](https://arxiv.org/abs/2506.10902).**  Given an arbitrary
extension

```text
0 -> I -> E -> D -> 0,
```

is

```text
dim_nuc(E) = max(dim_nuc(I), dim_nuc(D))?
```

The reverse inequality is automatic because nuclear dimension does not
increase on ideals or quotients.  Winter--Zacharias' general gluing argument
only gives

```text
dim_nuc(E) <= dim_nuc(I) + dim_nuc(D) + 1.
```

As of 2026-08-30 this remains open in the stated generality.  The May 2026
version of the 99-problems paper still asks it.  A search of the primary arXiv
catalogue through that date found no later paper claiming the arbitrary
extension theorem; the latest directly targeted paper remains Evington--Ng--
Sims--White, [arXiv:2409.12872v2](https://arxiv.org/abs/2409.12872), which
proves the maximum formula for extensions with stable Kirchberg ideal and
commutative unital quotient.  Other established positive cases include
separable commutative extensions, AF-by-AF extensions, quasidiagonal
extensions, essential extensions of commutative algebras by the compacts
([Gardner--Tikuisis](https://arxiv.org/abs/2202.04695)), and the special
`O_infinity`-stable cases in
[Evington](https://arxiv.org/abs/2012.03650).

The repository now removes "separable" from the subhomogeneous case:
`stw82-subhomogeneous-maximum` proves
the formula whenever both endpoints are subhomogeneous, with no separability
hypothesis.  In particular, arbitrary commutative extensions obey the
maximum formula.

The project reduction
`stw82-counterexamples-reflect-to-separable-extensions` shows that the word
"arbitrary" does not create a separate nonseparable frontier: every
counterexample would already have a separable subextension counterexample
with no larger endpoint dimensions.

## Attempts

The established route
`stw82-separable-maximum-implies-arbitrary-maximum` removes nonseparability
from the problem.  What remains is the separable maximum theorem.  The
standard quasicentral-approximate-unit proof produces disjoint ideal and
quotient approximations but gives their colours separate labels, yielding
the sum-plus-one bound.  Known optimal proofs reuse colours only after
obtaining extra orthogonality from the extension (for example a
quasidiagonal projectional approximate unit, or the classification inputs in
the Kirchberg-ideal cases).  No mechanism currently supplies that
orthogonality for an arbitrary separable extension.

The exact local obstruction is now recorded in
`stw82-order-zero-direct-sum-support-criterion`: two order-zero maps merge by
the direct-sum construction precisely when their unit supports are
orthogonal.  For the complementary supports `h` and `1-h`,
`stw82-complementary-cutdowns-merge-iff-near-projections` proves, with
explicit estimates, that asymptotic orthogonalizability is equivalent to
`h` being asymptotically projectional.  This is not a consequence of
quasicentrality.  Indeed,
`stw82-commutative-max-formula-with-maximal-cutdown-overlap` shows that in
the interval endpoint extension every positive contractive quasicentral
approximate unit has overlap norm exactly `1/4`, although the maximum
formula holds.  Thus the unresolved gluing step must reorganize the colour
maps or absorb their transition region; perturbing the two raw cuts cannot
be a general proof.
