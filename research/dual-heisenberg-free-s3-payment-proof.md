---
rg: 2
id: dual-heisenberg-free-s3-payment-proof
kind: route
title: Flip all sign atoms and count the transposition-fixed profiles
target: dual-heisenberg-frame-pays-free-s3-orbit
requires:
  - free-s3-atom-has-unit-opnorm-leakage
  - opnorm-packet-exactification-is-dimension-free
---

On the marked carrier `P`, the relations `(DHP1)` say

```text
rho(D_ij) rho(C_kl) rho(D_ij)^*
 =(-1)^(delta_(i,k)delta_(j,l)) rho(C_kl).             (1)
```

Consequently conjugation by `rho(D_ij)` carries `e_epsilon` to the atom
obtained by flipping the single sign `epsilon_ij`.  The nine flips act
transitively on all `2^9` sign vectors.  Unitary conjugacy therefore makes
all atom ranks equal, and their orthogonal sum is `P`.  This proves

```text
rank(e_epsilon)=2^(-9) rank(P).                        (2)
```

A transposition of three letters fixes one letter.  On the nine ordered
pairs its simultaneous row/column action therefore has one fixed point;
the other eight points form four two-cycles.  A sign vector is invariant
exactly when it is constant on these five cycles, so there are `2^5=32`
fixed sign vectors.  Summing `(2)` over them proves `(DHP4)`.

Equation `(DHP2)` conjugates `e_epsilon` to `e_(epsilon^tau)`.  Each fixed
atom is consequently preserved by `W_tau`, and so is their sum `Q_tau`.
This is `(DHP5)`.  Notice that no assertion is made about the action inside
one fixed atom: an arbitrary reservoir unitary is allowed there.  It does
not affect zero leakage because the whole fixed atom is reducing.

For the literal realization `(DHP3)`, the only possibly nontrivial cross
commutator is

```text
[x_(1,k_ij)(q),x_(k_kl,3)(q)]
 =x_13(q^2)=z
```

when `(i,j)=(k,l)`; otherwise the root indices are disjoint.  Same-row and
same-column roots commute.  Constant Weyl permutations fix endpoints
`1,3` and permute the middle indices, proving `(DHP1)--(DHP2)`.

All groups and matrix-unit tables used here are fixed and finite.  The
dimension-free exactification theorem therefore rounds an operator-norm
microstate to this exact packet with an error modulus depending only on the
packet.  Applying the exact calculation and conjugating the resulting
spectral projections back gives the robust final statement.

