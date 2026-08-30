---
rg: 2
id: stw82-diagonal-corner-projection-au-proof
kind: route
title: Add projection approximate units from the two complementary multiplier corners
target: stw82-real-rank-zero-multiplier-projections
requires:
  - stw82-internally-reduced-projection-exhaustions
artifacts:
  - research/artifacts/stw82-real-rank-zero-multiplier-audit-2026-08-30.md
---

Put `q=1-p`.  If `(u_n)` is a countable approximate unit for `A`, then
`(pu_np)` is an approximate unit for `pAp`, and similarly for `qAq`.
Thus both diagonal corners are sigma-unital.  Real rank zero passes to
hereditary subalgebras, and a sigma-unital real-rank-zero algebra has an
increasing approximate unit of projections.  Choose

```text
e_n in pAp,       f_n in qAq
```

with these properties, passing to simultaneous subsequences if necessary,
and set `Q_n=e_n+f_n`.  The two summands are orthogonal, so `(Q_n)` is an
increasing sequence of projections in `A subset M(A)`.  It commutes with
`p`, and `pQ_n=e_n in A`.

It remains to verify strict convergence, since neither diagonal approximate
unit is assumed quasicentral.  For `a in A`, let `x=pa`.  Then

```text
||(p-e_n)x||^2
 =||(p-e_n)xx^*(p-e_n)|| ->0,                           (RRMP2)
```

because `xx^*=paa^*p` belongs to `pAp` and `(e_n)` is an approximate unit
there.  Applying the same argument to `qa` and `(f_n)` gives

```text
||(1-Q_n)a||
 <=||(p-e_n)pa||+||(q-f_n)qa|| ->0.                    (RRMP3)
```

The right strict limit follows either by the analogous calculation with
`a^*p,a^*q`, or by applying `(RRMP3)` to `a^*` and taking adjoints.  Hence
`Q_n->1` strictly in `M(A)`.

All hypotheses of `stw82-internally-reduced-projection-exhaustions` now
hold, and `(RRMP1)` follows.  No assertion that `(Q_n)` is quasicentral in
`A` is used or needed.
