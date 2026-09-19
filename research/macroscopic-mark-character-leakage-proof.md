---
rg: 2
id: macroscopic-mark-character-leakage-proof
kind: route
title: Remove the trivial spectator from the three-fiber moving-marker model
target: macroscopic-mark-core-does-not-control-character-transport
requires:
  - sparse-marked-lamp-corner-has-unit-relative-leakage
---

Use the construction of the prerequisite.  Thus

```text
q:F(a,b)->C_3,             q(a)=1, q(b)=0,
F_y=q^(-1)(y),             r_(y,n)=b^(N_n)a^y,
E_(y,n)=F_y minus {r_(y,n)}.                              (1)
```

Let `chi_(y,n)` be the full lamp character supported on `E_(y,n)`.  Instead
of adjoining the growing trivial spectator from the sparse model, work on
exactly three orthogonal lines `P_0,P_1,P_2` and put

```text
rho_n(m)|_(P_y)=chi_(y,n)(m),
U_n(g)P_yU_n(g)^*=P_(y+q(g)).                            (2)
```

These are respectively exact representations of the entire lamp group and
of the actor.  The moving markers leave the support of every fixed lamp.
Therefore, for each fixed `g,m`,

```text
U_n(g)rho_n(m)U_n(g)^*=rho_n(g.m)                        (3)
```

for all sufficiently large `n`.  Hence
`sigma_n(m,g)=rho_n(m)U_n(g)` is a pointwise operator-norm asymptotic
representation, with every fixed covariance defect eventually equal to
zero.

The fixed lamp `w=m_e m_a` meets the quotient fibers `F_0,F_1` once and
misses `F_2`; its two positions are eventually different from every moving
marker.  Consequently

```text
rho_n(w)|_(P_0)=-1,       rho_n(w)|_(P_1)=-1,
rho_n(w)|_(P_2)=+1,       p_n=P_0+P_1.                   (4)
```

This proves `(MMC3)`.  Since `U_n(a)` cyclically permutes the three lines,

```text
U_n(a)p_nU_n(a)^*=P_1+P_2,
(P_0+P_1) join (P_1+P_2)=P_0+P_1+P_2=1,                (5)
```

which proves `(MMC4)`.

For a generator `s`, the prescribed translate of `chi_(y,n)` has support

```text
F_(y+q(s)) minus {s r_(y,n)},                            (6)
```

whereas the atom onto which `U_n(s)` sends `P_y` has support

```text
F_(y+q(s)) minus {r_(y+q(s),n)}.                         (7)
```

The free-group normal-form calculation in the prerequisite proves these two
characters are distinct for every `y` and each of the four generators.
It also proves that `(6)` is not either of the other two coordinate atoms.
Thus the prescribed target projection is zero while
`U_n(s)P_yU_n(s)^*=P_(y+q(s))`.  Each of the three rank-one atoms leaks its
full normalized trace `1/3`, proving total leakage `1`.  Summing only over
`y=0,1` gives leakage `2/3`, equal to `tr_3(p_n)`, and hence relative leakage
one.

The carrier is already the join of two conjugate marked supports, so no
restriction or reblocking based solely on those supports changes the model.

## Faithfully Hilbert--Schmidt separated variant

For completeness, the free lamplighter `Gamma` is residually finite by an
elementary finite-quotient argument.  Given a nonidentity `(m,g)`, choose a
finite quotient `q:F(a,b)->K` which either keeps `g` nontrivial, or, when
`g=1`, is injective on the finite support of the nonzero lamp `m`.  In the
latter case the pushed-forward lamp in `direct_sum_K C_2` remains nonzero.
The resulting map

```text
Gamma -> (direct_sum_K C_2) semidirect K                         (8)
```

separates `(m,g)`.  One obtains a quotient injective on any prescribed finite
set by taking a product of finitely many such quotients.  (Residual finiteness
of the rank-two free group itself follows, for example, by its action on the
finite folded graph obtained from the finite reduced-word ball containing
the prescribed nonidentity words.)

Enumerate `Gamma` and choose finite quotients `pi_n:Gamma->G_n` separating
the first `n` nonidentity elements.  Let `D_n=|G_n|` and let `lambda_n` be
the left regular representation of `G_n`.  Amplify the three-dimensional
moving-label model `D_n` times and form

```text
Sigma_n = (sigma_n^move tensor I_(D_n)) directSum
          (lambda_n o pi_n).                                  (9)
```

The two summands have dimensions `3D_n` and `D_n`, respectively.  For every
fixed `g!=1`, the regular summand eventually sends `g` to a nonidentity left
translation, whose normalized trace is zero and whose squared normalized
Hilbert--Schmidt distance from the identity is `2`.  Its weight in `(9)` is
`1/4`, proving

```text
liminf ||Sigma_n(g)-1||_2^2 >= (1/4)2=1/2.              (10)
```

The moving block contributes active mark rank `2D_n` out of total dimension
`4D_n`, already giving marked density `1/2`.  Its three atoms leak completely
and occupy weight `3/4`.  The finite-quotient regular block has exact actor
transport of its lamp characters and contributes nonnegative leakage.
Therefore total leakage is at least `3/4`, proving the remaining assertions.
