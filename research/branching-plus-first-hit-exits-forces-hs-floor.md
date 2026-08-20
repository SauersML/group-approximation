---
rg: 2
id: branching-plus-first-hit-exits-forces-hs-floor
kind: claim
title: A two-child recurrence makes one-copy first-hit exits preserve the active carrier
distinct_from:
  first-hit-carrier-contraction-ladder: that assumes carrier persistence as an input; this derives persistence from a supercritical two-child balance and the fact that at most one child copy exits.
  contractive-computation-ladder: that iterates a backward scalar contraction without an explicit reservoir; this combines forward branching with a summable first-hit reservoir.
  fanizza-turing-bcs-signal-collapse: that imports a polynomially certified projection recurrence; this is the abstract trace ledger after a groupification splits its two children into an active copy and an exit copy.
---

Let `q_0,...,q_N` be active carrier masses and `r_0,...,r_(N-1)` be
first-hit exit masses.  Suppose

```text
2 q_n <= q_(n+1)+r_n+delta_n,                          (BFE1)
r_n <= q_n+zeta_n,                                     (BFE2)
r_n >= eta q_n-epsilon_n,                              (BFE3)
sum_(n<N) r_n <= 1,                                    (BFE4)
```

where every error is nonnegative and `eta>0`.  Then

```text
q_0 <= q_n + sum_(j<n)(delta_j+zeta_j),                 (BFE5)
```

and consequently

```text
eta N q_0
 <= 1
  + eta sum_(j<N)(N-1-j)(delta_j+zeta_j)
  + sum_(n<N) epsilon_n.                               (BFE6)
```

Thus no separate compressor or invariant-corner theorem is needed merely to
obtain persistence.  The branching factor two pays for the loss of one exit
copy and leaves one active copy.

If, for a polynomial `p` and constants `A,B`,

```text
delta_n+zeta_n <= A p(n) sqrt(E),
epsilon_n       <= B p(n) sqrt(E),                     (BFE7)
```

and marked separation gives `q_0>=q_*>0`, choose any fixed
`N>1/(eta q_*)`.  Equations `(BFE6)--(BFE7)` give

```text
E >= ((eta N q_*-1)/C_N)^2 > 0,                        (BFE8)
```

where

```text
C_N=eta A sum_(j<N)(N-1-j)p(j)+B sum_(n<N)p(n).
```

All constants are independent of matrix dimension.  Applied to the Fanizza
recurrence, the remaining groupification obligations are exactly: realize
`(BFE1)` with its polynomial relator decomposition, identify the relative
Schur multiplicity bit as an exit satisfying `(BFE2)--(BFE3)`, and place those
exits in the summable E5 boundary layers `(BFE4)`.
