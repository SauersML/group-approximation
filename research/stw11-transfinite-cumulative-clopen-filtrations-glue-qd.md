---
rg: 2
id: stw11-transfinite-cumulative-clopen-filtrations-glue-qd
kind: claim
title: Transfinite cumulative compact-open support filtrations glue quasidiagonality
distinct_from:
  stw11-clopen-exhaustion-glues-qd: that treats one extension and finite chains by backward induction; this treats arbitrary continuous ordinal chains by building the cumulative open-support ideals forward and then making one final projectional cut.
  stw07-local-qd-subalgebras-force-quasidiagonality: that is the abstract norm-local permanence theorem; this identifies the dynamical cumulative-support condition which supplies its increasing quasidiagonal ideals and also controls the final quotient extension.
artifacts:
  - research/artifacts/stw11-transfinite-clopen-filtration-audit-2026-08-30.md
---

Let `Z^d` act on a compact metrisable space `X`.  Let `lambda` be an
ordinal and let

```text
X=Y_0 supseteq Y_1 supseteq ... supseteq Y_lambda
```

be a decreasing continuous chain of closed invariant subsets: at every
nonzero limit ordinal `delta<=lambda`,

```text
Y_delta=intersection_(beta<delta) Y_beta.
```

Put `U_beta=X\Y_beta`.  Assume:

1. for every `0<beta<=lambda`, the invariant open set `U_beta` has an
   increasing exhaustion by invariant compact-open subsets of `U_beta`;
2. every successor stratum algebra

   ```text
   C_0(Y_beta\Y_(beta+1)) rtimes Z^d       (beta<lambda)
   ```

   is quasidiagonal;
3. the terminal crossed product `C(Y_lambda) rtimes Z^d` is
   quasidiagonal.

Then `C(X) rtimes Z^d` is quasidiagonal.

Already for `lambda=omega`, this gives a genuinely infinite support-filtration
class: all finite prefixes may leave a nonquasidiagonal or otherwise
uncontrolled tail quotient, while the intersection subsystem and every
successor layer are quasidiagonal.  The extra condition is cumulative:
compact-open exhaustions are required for `X\Y_beta`, not only separately
inside the strata.  No restriction on the cofinality of `lambda` is needed;
at a limit stage compact support is captured by one earlier member of the
ordinal chain.  No AF-embedding conclusion is asserted.
