---
rg: 2
id: mark-fixed-relative-words-do-not-coerce-native-hecke-kernel
kind: claim
title: Mark-fixed relative words do not coerce a native Hecke kernel
invalidates:
  - mark-fixed-relative-word-kernel-authentication
artifacts:
  - research/mark-fixed-relative-word-kernel-no-go-proof.md
distinct_from:
  center-chain-mixed-relative-word-fixes-mark: that computes the exact action of the mixed Hecke relative word on the mark; this proves the quantitative consequence for kernel selection and native occurrence authentication.
  literal-prefix-whitehead-relative-word-fixes-mark: that treats the literal adjacent Whitehead subgroup; this combines both mark-fixed families and isolates the exact missing mixed-word spectral estimate.
  projective-row-data-do-not-authenticate-hecke-polars: that permits independent spectator gauges because only separate even-parity row data are tested; this uses a common spectator gauge which cancels even from the complete relative word, its braid/order data, and its mark action.
---

**ESTABLISHED MARK-FIXED KERNEL NO-GO.**  For both newly audited relative
word families one has

```text
U=u_1^(-1)u_2,                    [U,z]=0.             (MFK1)
```

For the literal adjacent prefix Whiteheads one additionally has `U^3=1`.
Consequently every kernel or low spectral cut formed only from `[U,z]` is
the whole marked carrier in every exact representation.  Neither `(MFK1)`
nor the order-three relation distinguishes the two individual transports
from any other pair with the same relative word.

This failure is quantitative.  Start with any realization in which two
candidate native transports agree with the Hecke maps `S_i:QH->PH`, where
`tau(Q)=t>0`.  Tensor with a balanced spectator involution `D` and replace
both native transports by

```text
N_i=S_i tensor D,                 i=1,2.               (MFK2)
```

The source and range projections are unchanged, individual square data are
unchanged when required, and the common gauge cancels from the relative
word:

```text
N_1^*N_2=S_1^*S_2 tensor 1.                            (MFK3)
```

Thus its mark action, order-three relation, and every relation expressed
through this relative word are unchanged.  The same common tensor factor
also preserves the adjacent braid relation.  However, if `E<=Q tensor 1`
has discarded mass `eta=t-tau(E)`, then

```text
||(N_i-S_i tensor 1)E||_2^2
 =4 tau(E(1-D)/2)
 >=4 max(0,t/2-eta).                                  (MFK4)
```

The last inequality is the projection trace inequality
`tau(EF)>=tau(E)+tau(F)-t` on the `Q` corner, with
`F=Q tensor (1-D)/2` of trace `t/2`.  Hence `eta=o(1)` forces the squared
comparison error for each row to be at least `2t-o(1)`.  Removing the gauge
requires discarding at least half of the fixed Hecke source, not a
vanishing amount.

The exact survivor can now be stated without ambiguity.  Let `T_(i,n)` be
the two actual relabeled native occurrence contractions, let `S_(i,n)` be
the rounded Hecke maps, and put on `Q_n`

```text
A_n=sum_(i=1)^2
 Q_n(T_(i,n)-S_(i,n))^*(T_(i,n)-S_(i,n))Q_n.          (MFK5)
```

For some fixed `alpha>0`, a mixed occurrence proof must derive from the
ordinary relator defect `delta_n` a dimension-independent estimate of the
form

```text
tau_n(Q_n 1_((C delta_n^(2alpha)),infinity)(A_n))
 <= C delta_n^alpha.                                  (MFK6)
```

The low spectral projection in `(MFK6)` would lose only
`O(delta_n^alpha)` source mass and give `O(delta_n^alpha)` comparison error;
the common Hecke maps then provide the matching range cut and relative
polar factorization.  Neither `(MFK1)` nor `U^3=1` controls `A_n`: their
defect is exactly zero in the spectator family `(MFK2)`, while `(MFK4)`
keeps the high spectral mass positive.

Thus the two mark-fixing results are negative audits, not the authenticated
mixed block which survived the finite-type firewall.  Closure still
requires an odd occurrence relation involving an individual native row and
an unequal-scale Hecke word, strong enough to prove `(MFK6)`, or an
equivalent normalized coercivity inequality.  A relative word which merely
fixes the mark cannot supply it.

DERIVATION
mark-fixed-relative-word-kernel-no-go-proof
