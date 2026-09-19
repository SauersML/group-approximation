---
rg: 2
id: regular-trace-forbids-fixed-finite-packet-rank-return
kind: claim
title: Fixed finite-packet projections cannot carry an unequal-rank unitary return
---

Let `Gamma` be a discrete group and let

```text
tau_reg : C^*_max(Gamma) -> C
```

be the trace obtained from the left regular representation.  If `F` is a
finite subgroup of `Gamma`, then `tau_reg` is faithful on the canonical copy
of `C[F]`.

Consequently, for projections `e,f` in finite subgroup algebras of `Gamma`,

```text
tau_reg(e) != tau_reg(f)
```

forbids unitary equivalence in `C^*_max(Gamma)`.  In particular, if `e,f` lie
in one finite packet algebra, `f <= e`, and a unitary `u` satisfies

```text
u e u^* = f,
```

then `e=f`.  Also, no nonzero finite-packet projection is properly infinite
in the full group C-star algebra.

This is a firewall for Property-(T)-free MF attacks.  A fixed finite packet
can provide semiprojective spectral cuts and exact rank ratios, but the
regular trace prevents the group relations themselves from identifying a
coarse packet projection with a strictly smaller fixed fine packet projection.
Any successful operator-norm return must therefore use a carrier selected
from the supplied representation (or a projection annihilated by the regular
representation), rather than two predetermined projections in finite subgroup
algebras.

**ESTABLISHED 2026-08-30** by
`regular-trace-fixed-packet-firewall-proof`.
