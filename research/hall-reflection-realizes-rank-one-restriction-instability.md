---
rg: 2
id: hall-reflection-realizes-rank-one-restriction-instability
kind: claim
title: Hall coset reflections realize the presentation-double instability on one vanishing-rank direction
distinct_from:
  shulman-double-forces-unstable-kernel-restriction: that obtains pointwise operator-norm unstable pairs from an injective norm-corona model of the whole double; this reproduces those pairwise quantifiers for one fixed cross word by finite coset actions and computes their vanishing tracial profile.
  shulman-presentation-double-witnesses-have-adjoint-normal-form: that extracts a global conjugating Julia unitary from Shulman's proof; this gives an explicit basepoint reflection already in that normal form, but does not model every word of the double simultaneously.
  finite-kernel-window-has-maximally-moving-zero-mode: that constructs a moving vector in a coset representation; this upgrades it to a conjugating unitary and computes the exact normalized-HS loss in the adjoint model.
---

**ESTABLISHED RANK-ONE CALIBRATION.** Let `Q=F/K` be an infinite simple
nonsofic quotient of a finitely generated free group, fix `f_0 in F\K`, and
choose an increasing exhaustion by finite sets `R_n subset K`. There are
finite-dimensional exact representations and involutions

```text
sigma_n:F->U(d_n),             V_n=V_n^*=V_n^(-1)       (HRR1)
```

such that

```text
[sigma_n(k),V_n]=0             for every k in R_n,
||[sigma_n(f_0),V_n]||_op=2,                            (HRR2)
```

but

```text
||Ad(sigma_n)(f_0)V_n-V_n||_(2,d_n)=sqrt(8/d_n)->0.    (HRR3)
```

Indeed Hall separability gives a finite-index subgroup `L_n<=F` containing
`<R_n>` but not `f_0`. Take `sigma_n` to be the permutation representation
on `ell^2(F/L_n)`, let `p_n` be the base-coset rank-one projection, and put

```text
V_n=1-2p_n.                                             (HRR4)
```

The first equation in `(HRR2)` is exact. The projections `p_n` and
`sigma_n(f_0)p_n sigma_n(f_0)^*` are orthogonal, giving the second equation
and `(HRR3)`. Necessarily `d_n=[F:L_n]->infinity`; otherwise a repeated
bounded-index subgroup would contain all of `K` while excluding `f_0`,
producing a forbidden nontrivial finite quotient of `Q`.

Set

```text
v_n=sigma_n,                 u_n=V_n sigma_n V_n.       (HRR5)
```

Then `u_n,v_n` are exact, agree eventually on every fixed `k in K`, and stay
operator-norm distance `2` apart at `f_0`. Under multiplication by `V_n`,
their left-right representation is exactly `Ad(sigma_n)`, as in the Shulman
Julia normal form. Thus the bare data

```text
pointwise operator agreement on K + fixed operator gap at f_0
```

can be carried by one rank-one coset defect whose normalized-HS mass tends
to zero. They imply no positive-rank moving spectral band, even after global
conjugacy of the two vertex representations is imposed.

There is a direct calibration against the three retention conditions.  In
the adjoint Hilbert space take the exact zero-energy line

```text
W_n=C V_n.                                               (HRR6)
```

For every fixed `f in F`, the two rank-one projections `p_n` and
`sigma_n(f)p_n sigma_n(f)^*` are equal or orthogonal.  Hence the normalized
unit vector `V_n/sqrt(d_n)` moves by at most `sqrt(8/d_n)`.  Projection onto
`W_n` therefore satisfies `(IR1)`, and `(HRR2)` gives `(IR2)` exactly for
every fixed kernel word eventually.  But `(HRR3)` says that `(IR3)` tends to
zero on the same line.  Thus even a moving exact spectral cutoff can be
almost `F`-reducing and kernel-trivial while retaining only an
operator-norm, not tracial, quotient wall.

This does not refute a more carefully chosen Shulman witness sequence or
`leavitt-positive-rank-intertwiner-retention`. It proves that a band-selection
lemma cannot use only `(PRI1)--(PRI3)` or `(SJA1)--(SJA3)`: it must consume
additional simultaneous-word structure of the faithful norm-corona model
that excludes the Hall reflection calibration.

DERIVATION
hall-coset-reflection-rank-one-proof
