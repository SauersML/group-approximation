---
rg: 2
id: full-pair-routing-of-complete-baseline-has-a-prefix-capacity-gap
kind: claim
title: Full-pair routing of every retained baseline type spends a fixed successor-prefix fraction
distinct_from:
  full-index-two-hnn-edge-creates-own-prefix-split: That proves the exact positive/negative split for one source; this shows why applying that cell to the complete retained baseline is incompatible with lossless perfect-model return.
  finite-packet-functoriality-has-positive-regular-profile: That gives a stationary regular-representation obstruction for a finite packet; this is a direct tracial capacity inequality requiring no regular representation or type-flow classification.
  balanced-schur-active-child-is-next-prefix-source: That still asks for a hybrid global incidence; this rules out the proposed assembly in which allowed and inactive baseline types are themselves all full-pair sources.
---

**ESTABLISHED.**  This is a no-go statement.  Let `Q` be a projection in a finite tracial von
Neumann algebra, let `B` be an involution commuting with `Q`, and write

```text
Q_+=Q(1+B)/2,                 Q_-=Q(1-B)/2.             (FPC1)
```

Suppose `A_1,...,A_T<=Q` are the mutually orthogonal retained type
projections of one complete baseline family.  Assume that every `A_i` is
routed by a full marked index-two cell sharing the target sign `B`.  Thus the
cell supplies a retained target `R_i<=Q_+` and a companion `S_i<=Q_-` with

```text
tau(R_i)=tau(S_i)=tau(A_i).                              (FPC2)
```

If a successor carrier `Q'<=Q_+` contains the returned retained family, then
lossless baseline return is impossible whenever `Q` is nonzero.  Indeed,

```text
tau(Q)-tau(Q') >= tau(Q_-)
                    >= max_i tau(S_i)
                     = max_i tau(A_i)
                    >= T^(-1) sum_i tau(A_i).            (FPC3)
```

In particular, if the retained types partition the baseline,
`sum_i A_i=Q`, then

```text
tau(Q)-tau(Q') >= tau(Q)/T.                              (FPC4)
```

This is already a contradiction in the perfect BCS representation required
by the first-hit program.  There every forbidden source is zero, the complete
allowed/inactive retained family fills the current carrier, and the recurrence
must return it with `tau(Q')=tau(Q)>0`.  But `(FPC4)` forces a positive loss.
Equivalently, lossless return forces `Q_-=0`, whereas any nonzero full-pair
source creates a nonzero equal-trace projection under `Q_-`.

The same obstruction is dimension-independent and robust.  If

```text
sum_i tau(A_i) >= tau(Q)-epsilon_0,
tau(S_i) >= tau(A_i)-epsilon_1,
tau(Q') >= tau(Q)-epsilon_ret,                            (FPC5)
```

while `S_i<=Q_-` and `Q'<=Q_+` hold after fixed-packet correction, then

```text
tau(Q) <= epsilon_0+T(epsilon_1+epsilon_ret).             (FPC6)
```

Indeed, choose `i` with
`tau(A_i)>=(tau(Q)-epsilon_0)/T`.  Since `Q'` and `S_i` lie in the two
orthogonal `B` sectors,

```text
tau(Q)-epsilon_ret <= tau(Q')
                    <= tau(Q)-tau(S_i)
                    <= tau(Q)-tau(A_i)+epsilon_1,
```

which rearranges to `(FPC6)`.  When all errors are `O(sqrt(E))`, this gives a
fixed normalized-Hilbert--Schmidt defect floor on every carrier of fixed
positive trace.

For the cell in `full-index-two-hnn-edge-creates-own-prefix-split`, `(FPC2)`
is exactly the Reynolds identity

```text
e_(H_i)(1+B)/2,          e_(H_i)(1-B)/2.
```

No orthogonality among different companions is used; one companion of the
largest retained type already proves the bound.  Extra tag coordinates and
separate HNN letters therefore do not evade it.

The conclusion is specific but decisive for the current compiler design:
full-pair prefix cells may be attached to the **forbidden surplus**, which
vanishes in the perfect model, but they cannot also carry the complete
allowed/inactive baseline.  Any live construction of
`balanced-schur-active-child-is-next-prefix-source` must be hybrid: a
companion-free common-prefix return for the baseline, plus full-pair cells
only for the predicate-sensitive surplus.
