---
rg: 2
id: stw93-abstract-central-factorization-can-fail
kind: claim
title: Ambient self-commutator decompositions need not centralize in a relative commutant
distinct_from:
  stw93-central-commutator-lifting-is-trace-hinge: that theorem identifies central commutator lifting as the exact actual XCIII trace hinge; this countermodel proves that no abstract lifting lemma follows from ambient unique trace, uniform averaging, and a factor tracial quotient alone.
  stw93-saturated-slice-data-allow-residual-trace: that doubled-F(Z) model obstructs arguments using the saturated slice data; this model additionally realizes the bad algebra as a relative commutant inside a uniquely traced uniform-Dixmier norm ultraproduct.
  stw93-free-factor-central-sequences-are-tracially-scalar: that is an actual free-factor 2-norm conclusion; the countermodel here has no faithfully traced full free-factor diagonal and therefore isolates that missing input rather than contradicting it.
artifacts:
  - research/artifacts/stw93-central-factorization-no-go-audit-2026-08-30.md
---

There exist a uniquely traced unital C*-algebra `M` with uniform singleton
Dixmier averaging, a separable unital subalgebra `B subset M`, and

```text
D_0=M intersect B',             I_0=J_tau intersect D_0,
```

such that

1. `D_0/I_0` is a II_1 factor;
2. `(I_0)_sa subset Com_sa(M)`; but
3. `(I_0)_sa` is not contained in `Com_sa(D_0)`.

Indeed there is a projection `p in I_0` and a normalized trace `s` on
`D_0` with `s(p)=1`, although `p in Com_sa(M)`.  Consequently there is no
general finite-factorization procedure which takes ambient
self-commutator approximations of a relative-central trace-kernel element
and replaces their factors by relative-central ones while preserving the
self-commutator sum.

The model also shows why orthogonal central cutdowns do not repair the
problem: block assembly preserves the maximum operator-norm commutator
defect rather than averaging it.  What the model deliberately lacks is the
faithfully traced diagonal copy of `C*_r(F_2) tensor Z`; its defining
subalgebra contains the trace-zero projection `p`.  Thus it does not refute
XCIII, but proves that a successful centralization argument must use the
faithfulness and free-factor structure of the actual diagonal inclusion.
