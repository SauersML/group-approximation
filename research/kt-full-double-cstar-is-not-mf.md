---
rg: 2
id: kt-full-double-cstar-is-not-mf
kind: claim
title: The full q=2, d=3 Kun--Thom double C-star algebra is not MF
distinct_from:
  kt-double-reduced-cstar-is-mf: that is the still-open MF question for the reduced group C-star algebra; the regular quotient kills the maximal Kazhdan compression obstruction used here.
  symmetric-double-weak-mf: that embeds the abstract double group into an auxiliary MF amalgam; the present claim proves that the universal full group C-star algebra itself cannot embed into a norm matrix corona.
  reduced-amalgam-canonical-trace-is-mf: that asks for asymptotically isometric full-norm models carrying one trace; this is the trace-independent obstruction that refutes that target as stated.
artifacts:
  - GroupApproximation/Analysis/MaximalCStarParagraphEndpoint.lean
  - GroupApproximation/Analysis/MaximalGroupCStar.lean
---

Fix `q=2`, `d=3`, and `r>=3` in the explicit Kun--Thom Theorem E pair,

```text
Gamma=EL_r(F_2[x_1,x_2,x_3]),
G=EL_r(F_2[x_1^(+-1),x_2^(+-1),x_3^(+-1)]) rtimes SL_3(Z),
```

and put

```text
D=G *_Gamma G.
```

Then the maximal group C-star algebra `C*(D)` is not Dedekind finite, hence is
not stably finite and admits no MF embedding.

Indeed, either canonical vertex copy of `G` in `D` retains the positive
strict compressor `t=I+E_12`:

```text
t Gamma t^(-1)<Gamma.
```

Thus `D` itself carries a strict Kazhdan compression.  The established,
machine-checked `maximal-group-cstar-infinite-under-strict-compression`
applies directly to `D`: the Kazhdan projection of `Gamma` is strictly
dominated by its conjugate under the canonical unitary of `t`, producing a
proper isometry in `C*(D)`.

This does not bear on `C*_r(D)`.  The regular trace is faithful on the reduced
algebra and kills the proper-compression phenomenon when passing from the
maximal completion to the regular quotient.  It also does not rule out a
nonfaithful MF-trace notion on `C*(D)` that omits norm isometry.  It rules out
precisely an MF embedding, and therefore any trace model required to be
asymptotically isometric for the full norm.
