---
rg: 2
id: stw82-diagonal-corner-projection-au-proof
kind: route
title: Capture finite sets by projection cuts from the two complementary multiplier corners
target: stw82-real-rank-zero-multiplier-projections
requires: []
artifacts:
  - research/artifacts/stw82-real-rank-zero-multiplier-audit-2026-08-30.md
---

Put `q=1-p`.  Real rank zero passes to hereditary subalgebras, and the
projection-approximate-identity characterization of real rank zero applies
without sigma-unitality.  Thus `pAp` and `qAq` have approximate identities
consisting of projections.

For a finite set `F subset A` and `delta>0`, choose projections

```text
e in pAp,       f in qAq
```

far enough out in the two approximate identities for the estimates below
to be less than `delta` simultaneously for every `a in F`, and set
`Q=e+f`.  The two summands are orthogonal, so `Q` is a projection in
`A subset M(A)`.  It commutes with `p`, and `pQ=e in A`.

The off-diagonal estimates do not require quasicentrality.  For `a in A`,
let `x=pa`.  Along the projection approximate identity of `pAp`,

```text
||(p-e)x||^2
 =||(p-e)xx^*(p-e)|| ->0,                               (RRMP2)
```

because `xx^*=paa^*p` belongs to `pAp`.  Applying the same argument to
`qa` and the projection approximate identity of `qAq`, and applying both
estimates to `a^*`, shows that `e,f` can be chosen with

```text
||(1-Q)a||<delta,       ||a(1-Q)||<delta               (RRMP3)
```

simultaneously for `a in F`.  Hence

```text
||a-QaQ|| <= ||(1-Q)a||+||Qa(1-Q)|| <2delta.           (RRMP4)
```

Now set `A_Q=QAQ` and `r_Q=p(1-Q)`.  Exact commutation gives
`r_QA_Q=A_Qr_Q=0`, while `pQ=e in A_Q`.  Therefore

```text
B_Q=C*(A_Q,p)=A_Q direct_sum C r_Q.                    (RRMP5)
```

Hereditary permanence gives
`dim_nuc(B_Q)<=dim_nuc(A)`.  For a finite subset of `A+C p`, first collect
its finitely many `A`-parts in `F`; `(RRMP4)` approximates those parts by
`A_Q`, and `p` belongs to `B_Q` exactly.  Thus `A+C p` is locally
approximated by subalgebras of nuclear dimension at most `dim_nuc(A)`.

For completeness, this local approximation implies the same nuclear-
dimension bound directly.  Approximate the chosen finite set into one
`B_Q`, and take a `d`-decomposable approximation

```text
B_Q -> F_0 direct_sum ... direct_sum F_d -> B_Q
```

for the nearby elements.  Extend each coordinate of the incoming c.p.c.
map from `B_Q` to `A+C p` by Arveson's extension theorem (unitizing when
necessary), and take their direct sum.  Compose the unchanged order-zero
return maps with the inclusion `B_Q subset A+C p`.  Contractivity and all
`d+1` order-zero colours are preserved, while the two finite-set errors
add.  The argument is vacuous when `dim_nuc(A)=infinity`.

This proves the upper bound in `(RRMP1)`.  The reverse inequality follows
from ideal permanence because `A ideal A+C p`.  No assertion that the cuts
are nested or quasicentral in `A` is used or needed.
