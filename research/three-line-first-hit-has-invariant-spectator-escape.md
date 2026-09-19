---
rg: 2
id: three-line-first-hit-has-invariant-spectator-escape
kind: claim
title: The three-line first-hit table has an exact invariant spectator escape
distinct_from:
  three-line-first-hit-solves-local-morita-edge: That constructs the useful oriented subsets at one edge; this gives an exact representation with visible source root but zero oriented-source mass.
  finite-schur-head-has-trace-character-escape: That produces an inner-invariant character on the entire finite Toeplitz head; this is the minimal three-coordinate obstruction at one adaptive edge.
  orthogonal-steinberg-root-spectral-support-is-not-additive: That uses a regular representation of a full elementary group; this uses a one-dimensional character of the local normalizer table and pinpoints the double-spectator condition.
---

**ESTABLISHED LOCAL FIREWALL.**  Let

```text
G_loc=F_p^3 rtimes <w>,       w(u,v,z)w^(-1)=(u,z,v),
```

where `w^2=1`.  Choose a nontrivial additive character `psi:F_p->T` and
define

```text
chi(u,v,z)=psi(v+z).                                  (TSE1)
```

Then `chi` is fixed by the swap, so it extends to a one-dimensional unitary
representation of `G_loc` by sending `w` to `1`.  In that representation
both the source coordinate `(0,1,0)` and destination coordinate `(0,0,1)`
are nontrivial, but the Fourier PVM is supported only at the character
coordinate `(0,1,1)`.  Therefore the oriented first-hit sets

```text
Omega_a={(0,v,0):v!=0},       Omega_d={(0,0,z):z!=0}
```

from `three-line-first-hit-solves-local-morita-edge` both have projection zero.
The full source-root spectral support is nevertheless the identity.

Thus the additive three-line table, its exact source--destination swap, and
arbitrary repetition of those relations do not imply the conditioned-source
bound `(TLF5)`.  The missing relation must rule out simultaneous source and
destination character charge.  In the coefficient language it must use a
transverse multiplication/commutator row or a genuinely matrix-only payload
constraint; inner normalizer covariance of this finite table is insufficient.
