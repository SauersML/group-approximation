---
rg: 2
id: stw93-mixed-z-slice-si-forces-infinite-capacity
kind: claim
title: Mixed-source Jiang--Su slice (SI) forces infinite central Cuntz capacity
distinct_from:
  stw93-property-si-holds-on-the-jiang-su-central-slice: that theorem treats pairs whose source and target both lie in the canonical Jiang--Su slice; this reduction allows an arbitrary source in the full XCIII trace-kernel ideal but only asks for targets in one fixed Jiang--Su copy.
  stw93-singular-trace-needs-finite-central-cuntz-capacity: that theorem extracts a finite-capacity cut from an extra trace; this theorem gives a sufficient local (SI) statement which rules out every such cut.
  stw99-problem-xciii-free-group-jiang-su-si: that is the full problem; the mixed-source statement here only closes the ordinary-trace capacity hinge and makes no quasitrace-linearity assertion.
artifacts:
  - research/artifacts/stw93-mixed-slice-capacity-audit-2026-08-30.md
---

Put

```text
A=C*_r(F_2) tensor Z,       D=A_omega intersect A',
I=J_tau intersect D.
```

Fix a unital central embedding `theta:Z->D` obtained from the canonical
Jiang--Su tensor-factor slice.  Consider the following strictly weaker
target-restricted fragment of property (SI):

```text
(MSI)  if e in I_+ is a contraction and f in theta(Z)_+ is a contraction
       with inf_(m>=1) tau_omega(f^m)>0, then some s in D satisfies
       s*s=e and fs=s.
```

If `(MSI)` holds, then every nonzero spectral cut of every positive element
of `I` has infinite central Cuntz capacity.  More precisely, for every
`e in I_+` and every `n>=1`,

```text
n[e]<=[1_D] in Cu(D).                                      (1)
```

Consequently every normalized trace on `D` annihilates `I`.  Equivalently,
the canonical limit trace is the unique normalized ordinary trace on `D`.

Thus the capacity attack on XCIII does not require property (SI) for
arbitrary large targets.  It is enough to prove property (SI) for an
arbitrary trace-kernel **source** and targets in one fixed central copy of
`Z`.  The presently established same-slice theorem does not supply this
mixed-source step.
