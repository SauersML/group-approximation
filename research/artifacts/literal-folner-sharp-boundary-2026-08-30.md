---
rg: 2
title: Sharp boundary and nonexactness audit for the literal factorization models
kind: artifact
---

# Exact boundary computation

Put `K=ker(E->Z)`, `A=C*_(max)(K)`, and use the regular Hilbert-`A`
module representation of `A rtimes_(alpha,r) Z` on
`ell^2(Z) tensor A`.  With the convention of the established
factorization route,

```text
Lambda(u)e_j=e_(j+1).
```

For `F=[-L,L]` and `N=2L+1`, let `P=P_F` and `S=P Lambda(u)P`.
Then

```text
S e_j = e_(j+1)  (j<L),       S e_L=0,
S*e_j = e_(j-1)  (j>-L),      S*e_(-L)=0.
```

Hence, exactly,

```text
S*S=I-p_L,                    SS*=I-p_(-L).             (B1)
```

The coefficient of every nonzero entry is `1_A`.  Every u.c.p. extension
`phi:A->M_|Q|` used by the factorization proof is unital, so the final map
`Phi_F=(id tensor phi) kappa_F` satisfies

```text
Phi_F(u)=S tensor I_Q,         Phi_F(u*)=S* tensor I_Q. (B2)
```

Combining unitality, `uu*=u*u=1`, (B1), and (B2),

```text
D_-=Phi_F(uu*)-Phi_F(u)Phi_F(u*)=p_(-L) tensor I_Q,
D_+=Phi_F(u*u)-Phi_F(u*)Phi_F(u)=p_L tensor I_Q.        (B3)
```

Both are projections of rank `|Q|` in `M_(N|Q|)`.  Therefore

```text
||D_+||=||D_-||=1,
||D_+||_(2,tr)=||D_-||_(2,tr)=1/sqrt(N),
tr(D_+)=tr(D_-)=1/N.                                  (B4)
```

This improves the general boundary estimate
`sqrt(2R/N)` to the exact constant `1/sqrt(N)` on the stable-letter
pair.  It also proves that increasing the Folner window can make the
normalized rank disappear while doing literally nothing to the operator
norm.

# Trace bookkeeping

On the stable-letter packet, `tr(Phi_F(u^r))=0` for every nonzero
`r` with `|r|<N`, because the compressed shift has zero diagonal.
The unit has trace one.  For a general finite Fourier packet, the finite
quotient in the established construction separates the finitely many
nonidentity diagonal coefficients, so `tr compose Phi_F=tau_E` exactly
on that packet.  Thus trace error is zero while the multiplicativity error
on `(u,u*)` is simultaneously

```text
operator norm = 1,       normalized HS norm = N^(-1/2).
```

# Nonexactness consequence

For any nonamenable factorization-property group `G`, suppose
`C*_(max)(G)` were exact.  Its GNS quotient onto `C*_r(G)` would be
locally liftable by Effros--Haagerup.  The amenable full canonical trace
would descend to an amenable reduced trace.  A reduced hypertrace restricted
to the diagonal `ell^infinity(G)` is a left-invariant mean, contradicting
nonamenability.

The literal group contains the retracted copy of `SL_3(Z)` displayed by
its split normal form, hence is nonamenable.  Its newly established
factorization property therefore makes its full group algebra nonexact.
This is independent of its already established LLP failure: the latter is
inherited from the `SL_3(Z)` subgroup, whereas nonexactness uses the
amenable full trace and its nonamenable GNS quotient.

# Scope

The sharp boundary formula describes the concrete Folner--finite-quotient
u.c.p. maps.  It is not a universal lower bound for all amenability models.
The nonquasidiagonality theorem supplies the universal obstruction, but its
finite test and threshold remain noneffective; the separate root
`effective-transport-modulus` is therefore not claimed closed here.
