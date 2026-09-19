---
rg: 2
id: multi-telescope-coset-action-and-double-proof
kind: route
title: Approximate a commuting compressor telescope one cyclic direction at a time
target: commuting-kun-thom-compressors-are-relatively-embeddable
requires:
  - monomial-ascending-hnn-coset-action-sofic
  - ascending-hnn-action-iff-iterated-cosets
  - sofic-coset-action-makes-amalgam-double-sofic
---

Let `alpha_i` be the self-embedding of `Gamma` induced by `A_i), and use
multi-index notation

```text
A^v=A_1^(v_1)...A_m^(v_m),       alpha^v=alpha_1^(v_1)...alpha_m^(v_m).
```

The maps commute.  Since `Q=<A_1,...,A_m>~=Z^m`, projection to the external
matrix factor gives

```text
P=N rtimes Q,
N=union_(v in N^m) Gamma_v,
Gamma_v=(a^v)^(-1) Gamma a^v.                               (MTC1)
```

The family `Gamma_v` is directed and increasing in every coordinate because
`a_i Gamma a_i^(-1) subset Gamma`.

## Multi-iterate separability

For `v in N^m`,

```text
alpha^v(Gamma)=EL_r(R_v),       R_v=k[A^v N^d].              (MTC2)
```

The columns of the injective integer matrix `A^v` freely generate the monoid
`A^v N^d`, so `R_v` is again a polynomial ring.  Suslin stability gives

```text
EL_r(R_v)=SL_r(R_v),            r>=3.                        (MTC3)
```

Take `g in Gamma` outside `alpha^v(Gamma)`.  By (MTC3), some entry of
`g` contains a monomial `x^w` with `w notin A^v N^d`.  Choose `M`
larger than every coordinate of every exponent in the finite support of that
entry and reduce

```text
k[N^d] -> Q_M=k[x_1,...,x_d]/(x_1^M,...,x_d^M).
```

The chosen monomial survives as a basis vector, while the image of `R_v` is
spanned by surviving monomials whose exponents lie in `A^v N^d`.  Therefore
the finite quotient `SL_r(Q_M)` separates `g` from
`alpha^v(Gamma)`.  Thus every multi-iterate in (MTC2), and every conjugate
of it in `Gamma`, is separable.

## Finite telescope windows

Put `X=P/Gamma`.  Take a finite multiplication window `F subset N`, a
finite set of sites `E subset X`, and `epsilon>0`.  Write each site as

```text
x=n_x a^(k_x) Gamma,       n_x in N, k_x in Z^m.
```

Choose `v in N^m` coordinatewise large enough that

```text
F subset Gamma_v,       n_x in Gamma_v,       v+k_x in N^m
```

for every `x in E`.  Conjugation by `a^v` identifies `Gamma_v` with
`Gamma`.  Write

```text
g=(a^v)^(-1) gamma a^v,       n_x=(a^v)^(-1)c_x a^v.
```

A direct stabilizer calculation gives

```text
g x=x
iff (a^(k_x))^(-1) n_x^(-1) g n_x a^(k_x) in Gamma
iff c_x^(-1) gamma c_x in alpha^(v+k_x)(Gamma).               (MTC4)
```

Hence the `Gamma_v`-orbit of `x` is a base coset action whose stabilizer,
after the displayed identification, is conjugate to
`alpha^(v+k_x)(Gamma)`.  The preceding separability produces exact finite
Schreier models.  Only finitely many orbits meet `E), so their disjoint
union gives one model for the prescribed `F,E,epsilon` window.  Since every
finite `N`-window is swallowed in this way, `N action X` is sofic.

## Adjoin the commuting directions

Let

```text
P_j=N rtimes <a_1,...,a_j>,       0<=j<=m.
```

Because the `a_i` commute, `P_j` is normal in `P_(j+1)` and the quotient
is infinite cyclic.  The cyclic-extension permanence theorem for sofic
actions, the same ingredient used in
`ascending-hnn-action-iff-iterated-cosets`, applies successively:

```text
N action X sofic
=> P_1 action X sofic
=> ...
=> P_m=P action X sofic.                                      (MTC5)
```

Restriction to the orbit of `Gamma` gives the claimed sofic action on
`P/Gamma`.

The ambient Kun--Thom group is residually finite, so its subgroup `P` is
sofic.  Apply `sofic-coset-action-makes-amalgam-double-sofic` to (MTC5):
`P *_Gamma P` is sofic.  Finally, each nonzero power of `a_1` has nonzero
image in the free-abelian quotient `Q`, so it lies outside `Gamma).
The Haar-relative-unitary part of the same theorem gives
`L(Gamma) subset L(P)` relatively embeddable over the scalars.

For the advertised pair, `E_12 E_13=E_13 E_12=0`, and

```text
(I+E_12)^p (I+E_13)^q=I+pE_12+qE_13.
```

Thus the two matrices commute and generate `Z^2).  Each sends one coordinate
monomial to its product with `x_1`, so each monoid image is proper.  This
verifies all hypotheses for the explicit two-compressor slice.
