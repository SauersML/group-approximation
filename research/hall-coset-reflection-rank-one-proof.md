---
rg: 2
id: hall-coset-reflection-rank-one-proof
kind: route
title: Reflect one separated coset and calculate its adjoint Hilbert--Schmidt mass
target: hall-reflection-realizes-rank-one-restriction-instability
requires:
  - simple-map-quotient-has-rigid-fd-restriction
---

For each `n`, put `H_n=<R_n>`. Since `H_n<=K` and `f_0 notin K`, Hall's
theorem gives a finite-index `L_n<=F` such that

```text
H_n<=L_n,                         f_0 notin L_n.         (HRP1)
```

Let `sigma_n` be the left permutation representation on `ell^2(F/L_n)`.
For the basepoint projection `p_n=|delta_(L_n)><delta_(L_n)|`, every
`k in R_n` fixes `p_n`. Hence `V_n=1-2p_n` commutes with `sigma_n(k)`.

Put `p_n'=sigma_n(f_0)p_n sigma_n(f_0)^*`. The two cosets in `(HRP1)` are
distinct, so `p_n p_n'=0`. Therefore

```text
Ad(sigma_n)(f_0)V_n-V_n=2(p_n-p_n'),                  (HRP2)
```

whose operator norm is `2` and whose squared normalized Hilbert--Schmidt
norm is

```text
tr_(d_n)(4(p_n+p_n'))=8/d_n.                          (HRP3)
```

The additive commutator has the same operator norm, since multiplication by
unitaries turns it into `(HRP2)`.

For any `f in F`, not only `f_0`, the basepoint projections `p_n` and
`sigma_n(f)p_n sigma_n(f)^*` are either equal or orthogonal.  Repeating
`(HRP2)--(HRP3)` therefore gives

```text
||Ad(sigma_n)(f)V_n-V_n||_(2,d_n)<=sqrt(8/d_n).        (HRP4)
```

On the one-dimensional space `W_n=C V_n`, the off-diagonal leakage of
`Ad(sigma_n)(f)` is bounded by the displacement in `(HRP4)`.  This proves
`(IR1)`.  Every fixed `k in K` belongs to `R_n` eventually and fixes `V_n`,
which proves `(IR2)`.  At `f_0`, `(HRP3)` tends to zero, so `(IR3)` fails.

If the indices `d_n` had a bounded subsequence, finitely generated `F` would
have only finitely many subgroups of those bounded indices. One subgroup
`L` would recur. The exhaustion then gives `K<=L`, while `(HRP1)` gives
`f_0 notin L`. Thus `L/K` would be a proper finite-index subgroup of `Q`, or
equivalently the core of `L` would give a nontrivial finite quotient of the
infinite simple group `Q`. This is impossible, so `d_n->infinity` after a
subsequence and `(HRP3)` tends to zero.

Finally `(HRR5)` gives exact representations. For `k in R_n`, conjugation
by `V_n` fixes `sigma_n(k)`, while for `f_0` its difference from
`sigma_n(f_0)` has norm `2`. The map `T |-> V_nT` identifies their left-right
action with `Ad(sigma_n)`, completing the calibration.
