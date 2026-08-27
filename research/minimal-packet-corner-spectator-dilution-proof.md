---
rg: 2
id: minimal-packet-corner-spectator-dilution-proof
kind: route
title: Compute the corner projection against trivial and irreducible multiplicity actions
target: minimal-packet-corner-overlap-has-irreducible-spectator-dilution
requires: []
---

Because `pi` is irreducible,

```text
End_Lambda(H_m,rho_m^flat)=I_n tensor M_m.
```

Choose matrix units `e_ab` in `M_m`.  An orthonormal basis of this
commutant in the unnormalized Hilbert--Schmidt inner product is

```text
u_ab=(I_n/sqrt(n)) tensor e_ab.
```

Since `C_P(X)=PXP`,

```text
||C_P(u_ab)||_HS^2
 =||(p/sqrt(n)) tensor e_ab||_HS^2
 =1/n.
```

The trace of a product of orthogonal projections is the sum of these
squared projected norms.  Therefore

```text
Tr_End(E_flat C_P)=m^2/n.
```

Dividing by `d^2=n^2m^2` gives the first identity in `(MCO3)`.

The tensor product of the irreducibles `pi` and `sigma_m` is irreducible for
`B times K`, so the other commutant is the scalar line.  Its normalized
Hilbert--Schmidt unit vector is `u=I_d/sqrt(d)`, and

```text
Tr_End(E_irr C_P)
 =<u,C_Pu>
 =Tr(P)/d
 =m/(nm)
 =1/n.
```

Division by `d^2=n^2m^2` proves the second identity in `(MCO3)`.

For the general formula, write `Ad_(rho(g))` for conjugation on `End(H)`.
The superoperator trace identity

```text
Tr_End(L_A R_B)=Tr(A)Tr(B)
```

and `C_P=L_P R_P` give

```text
Tr_End(C_P Ad_(rho(g)))=|Tr(P rho(g))|^2.
```

Haar averaging `Ad_(rho(g))` over the compact image closure is exactly
`E_Lambda`, proving `(MCO3b)`.  For irreducible `rho`, matrix-coefficient
orthogonality gives

```text
integral |Tr(P rho(g))|^2 d mu(g)=Tr(P^*P)/d=q,
```

which proves `(MCO3c)`.

Finally the orthogonal projection onto `span(P)` has ordinary superoperator
rank one, proving `(MCO4)`.  Equations `(MCO2)--(MCO4)` use no property of
the packet beyond irreducibility and minimality of `p`, while every packet
operator in both models is literally `pi(b) tensor I_m`.  Hence all local
packet relations and moments agree exactly despite the overlap dilution.
