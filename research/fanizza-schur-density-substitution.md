---
rg: 2
id: fanizza-schur-density-substitution
kind: claim
title: Fanizza polynomial certificates survive exact Schur character-density substitution
distinct_from:
  fanizza-bcs-polynomial-doubling-tape: that supplies a polynomial relator-ideal decomposition in the BCS algebra; this replaces every nonlinear projection relator by an explicit finite sum of group words and tracks normalized-HS cost.
  schur-predicate-is-character-density-difference: that treats one predicate exactly; this substitutes the complete fixed Fanizza predicate menu throughout the level-dependent recurrence certificate.
  relative-rank-one-fanizza-groupification: that must construct ordinary group relators paying every substituted density gap; this proves no additional nonlinear or runtime-dependent loss occurs once such payment is available.
---

For the fixed nonlinear predicate menu in the Fanizza BCS, attach the Schur
packet inclusion `C_c<=B_c` of baseline dimension `D_c` to every occurrence
`c`, and put

```text
G_c=Z_(C_c)-Z_(B_c).                                  (FDS1)
```

The level-`n` Fanizza recurrence residual admits an effective decomposition

```text
R_n
 =sum_(ell in L_n) A_ell (2D_(c(ell))G_(c(ell))) B_ell
  +sum_(j in J_n) C_j r_j D_j,                        (FDS2)
```

after exactification of the fixed packet tables. Here the first sum replaces
the nonlinear forbidden-projection relators, the `r_j` are the remaining
linear/commutation and packet-table relators, all coefficient evaluations are
uniformly bounded, and the total certificate size is at most

```text
C((n+1)m)^k.                                          (FDS3)
```

The constants and the finite list of packet dimensions depend only on the
machine-independent predicate menu, not on matrix dimension, computation
level, or halting time.

Consequently, for an approximate finite-dimensional tuple of background
relator energy `E_0`, fixed-packet correction loss `E_pkt`, and occurrence
density-gap energy

```text
E_G(n)=sum_(ell in L_n)||G_(c(ell))||_2^2,
```

one has

```text
||R_n||_2
 <= C_1((n+1)m)^k sqrt(E_0+E_pkt)
    +C_2((n+1)m)^(k/2) sqrt(E_G(n)).                  (FDS4)
```

Thus the Schur substitution preserves the polynomial-versus-exponential
accounting in the Fanizza argument. To close the groupification it is enough
to construct a finite presentation with a bounded-overlap estimate

```text
sum_c ||Z_(C_c)-Z_(B_c)||_2^2 <= C_ret E_group.        (FDS5)
```

No nonlinear scalar selector, individual irreducible-copy choice, or
dimension-dependent packet table is needed beyond `(FDS5)`.

The estimate `(FDS5)` cannot itself be obtained by placing each `G_c` in the
ordinary group relator ideal while preserving the packet carrier:
`schur-density-gap-has-no-direct-relator-certificate` rules that out. It must
come from a finite-dimensional rigidity/recurrence theorem rather than a
second sparse algebraic substitution.
