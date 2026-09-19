---
rg: 2
id: effective-transport-modulus
kind: claim
title: Explicit numerical modulus for the literal operator-norm obstruction
root: true
distinct_from:
  uniform-finite-mf-obstruction: The established compactness theorem gives an unspecified finite test and positive threshold; this claim asks for a computed modulus on the displayed relators from the rational Kazhdan gap.
artifacts:
  - non_mf_groups_exist.tex
  - notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
---

Compute an explicit positive defect threshold and error function, directly
from the rational property-(T) certificate and the forty-one displayed
relators, that force every finite-dimensional approximate model to send the
marked word close to the identity uniformly in the dimension.

## Attempts

- `literal-base-explicit-kazhdan-pair` supplies an explicit honest
  eight-word affine Kazhdan pair with
  `kappaB=1/(5*sqrt(3000)+2)`.
- `p13-rotation-relator-defect-219` expands the checked short-word replay:
  rotation-relator defect `delta` makes the thirteen substituted P13
  relators have individual costs
  `(59,122,116,68,59,60,43,18,16,37,37,39,219)*delta`.
- `p13-hodge-robust-rotation-gap` now propagates those individual costs
  through all 484 Hodge support products and the Fox-prefix canonicalization.
  It proves the explicit defective-tuple inequality

```text
(gamma - 6692*delta - 599314*delta^2) * rotation_energy
  <= squared_laplacian_norm + 196350*delta^2*squared_norm,
gamma = 28329113480286/10^16,
```

  and a rotation spectral split for
  `delta < 3.7381134709e-7`. The finite P13 SOS/replay aggregation is
  therefore closed.
- The current first mathematical gate is affine. The exact property-(T)
  bridge uses an exactly rotation-fixed projection and arbitrarily long
  rotation conjugators in the two-conjugate translation normal form. The
  robust P13 theorem gives a low spectral cluster, not an exact fixed
  subspace, so naive relator telescoping is not uniform. A full-base rational
  sum-of-squares certificate or an explicit robust relative-property-(T)
  theorem is still needed.
- `p13-low-cluster-does-not-control-long-rotation-words` proves that this
  obstruction is sharp for the direct circumcenter robustification. On the
  scalar tuple
  `v1=v2=v3=1, X=exp(i*pi/n), Y=Z=1`, all twelve nonrotation base
  relators are exact, the rotation defect is at most `6*pi/n`, and the
  P13 energy is at most `22*pi^2/n^2`; nevertheless
  `(ZXY)^n=-1`. Thus no modulus tending to zero can make every escaping
  rotation conjugator almost fix every P13-low vector. This does not refute
  a full affine gap, but it rules out closing it by ordinary word telescoping
  after merely replacing the exact rotation-fixed projection by the low
  spectral projection.
- `post-gap-compressor-constants` closes the dimension-free analytic
  vector chain once its three stage inputs are supplied. If `f` is the
  top-corner fixing error, `ell` the reverse leakage, and `c` the
  normalized capture mass, then transported displacement is at most
  `2*f^2 + 16*ell^2 + 16*c`, and the marked commutator is at most
  `8*f^2 + 64*ell^2 + 64*c`. The committed budget
  `f^2=epsilon/24` and `ell^2=c=epsilon/192` is exact.
- `literal-transport-gap-step-is-noneffective` audits that the current Lean
  transport route still calls
  `WeakMFVectorGNS.hermitianAverage_eventually_no_intermediate_eigenvalues`,
  an ultralimit contradiction with an unspecified `exists N`. After a
  robust affine gap replaces that call, what remains is presentation-specific
  finite replay: instantiate top-corner fixing, rotated-Laplacian leakage,
  root capture, and the fixed compressor/marked-word products from the
  displayed relators. The downstream analytic inequalities themselves are
  no longer missing.
- Source drift: `non_mf_groups_exist.tex` is now the Leavitt manuscript and
  no longer displays the former forty-one-relator presentation. The legacy
  literal Lean modules and research nodes remain, but the artifact pointer
  above must be restored or replaced before a literal manuscript-level
  modulus can be advertised.

**OPEN.** No positive numerical relator threshold for the full marked-word
conclusion is justified yet.
