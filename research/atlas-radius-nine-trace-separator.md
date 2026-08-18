---
rg: 2
id: atlas-radius-nine-trace-separator
kind: claim
title: The first mixed atlas window already carries a matrix-only trace separator
distinct_from:
  atlas-matricial-trace-separator: that unrestricted certificate interface is too close to Hahn--Banach duality for nonhyperlinearity; this claim fixes the trace-word support to the first structurally nontrivial atlas window, X-length at most nine, and is therefore a strictly stronger finite search target.
  atlas-kernel-window-length-nine: that proves length nine is the first point where the atlas kernel escapes the retraction screen; it does not assert any matrix-trace separation.
artifacts:
  - research/artifacts/nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md
---

Let `T_St` and `Gamma_St` be the explicit rank-five atlas/Steinberg
presentation from `atlas-steinberg-rank-five-translation`.  There are rational
coefficients `a_w` supported only on reduced trace words `w` of atlas X-length
at most `9`, and rational constants `C,c>0`, such that the self-adjoint linear
trace polynomial

```text
P(U) = a_e + sum_(1 <= |w|_X <= 9) a_w Re tr_n(w(U))
```

obeys

```text
P(U) + C * sum_(r in T_St) ||r(U)-1||_2^2 >= 0
```

for every matrix size `n` and every unitary twelve-tuple `U`, whereas

```text
P(lambda_Gamma_St) <= -c
```

for the canonical group trace.

The cutoff `9` is mathematically motivated rather than cosmetic:
`atlas-kernel-window-length-nine` proves that every atlas kernel word of
X-length at most `8` lies behind the retraction obstruction, while length `9`
is the first window containing a kernel word that escapes it.  Thus this asks
whether the **first genuinely mixed finite window** already exposes the
matricial/nonmatricial gap.

Unlike unrestricted finite-word separation, existence of a radius-nine
certificate is not automatic from a hypothetical nonhyperlinearity theorem;
it can fail while a higher-radius separator exists.  It is therefore a genuine
bounded-complexity theorem target and a finite coefficient search problem.

## Attempts

- Enumerate the X-length-`<=9` trace-word orbits under the obvious atlas chart
  and inversion symmetries.  Use certified canonical group reductions where
  available to obtain the target moment vector.
- Search dual linear/semidefinite functionals against finite-dimensional
  unitary samples with the exact `T_St` defect penalty, then rationally
  reconstruct stable orbit coefficients.  Finite-size numerics are discovery
  only: the surviving candidate still needs an all-matrix-size proof.
- Use the existing radius-five boundary data to seed the basis: prioritize the
  cyclic classes that first escape the retraction screen rather than all short
  words uniformly.
- For any candidate, try to prove the all-`n` inequality by a genuinely
  matricial invariant-theory argument.  Reject immediately any derivation that
  is valid in every tracial von Neumann algebra, by
  `global-tracial-positivity-cannot-separate-group-trace`.
