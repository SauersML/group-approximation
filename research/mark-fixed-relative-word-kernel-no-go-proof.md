---
rg: 2
id: mark-fixed-relative-word-kernel-no-go-proof
kind: route
title: Cancel a common spectator gauge from both mark-fixed relative transports
target: mark-fixed-relative-words-do-not-coerce-native-hecke-kernel
requires:
  - center-chain-mixed-relative-word-fixes-mark
  - literal-prefix-whitehead-relative-word-fixes-mark
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - projective-row-data-do-not-authenticate-hecke-polars
---

Both audited word calculations give `[U,z]=0` as an exact group identity,
so functional calculus of its commutator has no nontrivial kernel or
spectral information.  To see that retaining the full relative word does
not help, let `D=D^*=D^(-1)` have equal positive and negative multiplicity
and commute with the original model.  Gauge both transports by the same
spectator factor.  It cancels in `N_1^*N_2`, and `D^2=1` preserves squares.
In a three-letter braid, each side contains three gauged transports and
therefore acquires the same final factor `D`.  Thus all the relative-word,
order, braid, support, and mark-centralizing equations used by the proposed
route retain zero defect.

Let `F=Q tensor (1-D)/2`, so `tau(F)=t/2`.  For any projection
`E<=Q tensor 1`, cyclicity gives

```text
||(S_i tensor (D-1))E||_2^2=4tau(EF).                 (1)
```

The elementary dimension inequality for two projections in a finite
tracial algebra gives

```text
tau(EF)>=tau(E)+tau(F)-tau(Q tensor 1)
        =t/2-eta.                                      (2)
```

Equations `(1)--(2)` prove `(MFK4)`.  In particular no estimate charging
the individual native/Hecke discrepancy to the relative commutator or its
order/braid defects can hold, since all those defects are zero while the
discrepancy stays positive on every vanishing-loss cut.  Formula `(MFK6)`
is exactly the extra coercivity statement not furnished by either newly
established mark-fixing identity.
