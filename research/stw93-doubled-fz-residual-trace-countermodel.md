---
rg: 2
id: stw93-doubled-fz-residual-trace-countermodel
kind: route
title: Double the Jiang--Su central sequence algebra and hide one factor in the trace kernel
target: stw93-saturated-slice-data-allow-residual-trace
requires:
  - stw93-tensor-factor-central-quasitrace-rigidity
  - stw93-jiang-su-slice-exhausts-tracial-central-quotient
artifacts:
  - research/artifacts/stw93-residual-bounded-trace-audit-2026-08-30.md
---

Let

```text
G=F(Z),             J={x in G:tau_G(x*x)=0},
Q=G/J.
```

The normalized `2`-quasitrace `tau_G` on `G` is unique, and `Q` is the
hyperfinite tracial central sequence II_1 factor.  Define

```text
D_0=G direct_sum G,                 tau_0(x,y)=tau_G(x),
I_0=J direct_sum G.
```

Then `I_0` is exactly the square-null ideal of `tau_0`, and

```text
D_0/I_0 ~= Q.
```

Use the diagonal embedding `delta:G->D_0` as the canonical slice.  Every
`(x,y) in D_0` decomposes as

```text
(x,y)=delta(x)+(0,y-x),
```

with the second summand in `I_0`; hence `D_0=I_0+delta(G)`, and the slice
maps onto `D_0/I_0` with kernel `J`.

Now let `Theta:G->D_0` be any unital homomorphism and write its coordinate
maps as `Theta_1,Theta_2:G->G`.  Uniqueness of `tau_G` gives

```text
tau_G o Theta_1=tau_G=tau_G o Theta_2.                    (1)
```

In particular `tau_0 o Theta=tau_G`, so automatic trace preservation holds,
and `(1)` places `Theta(J)` inside `J direct_sum J`.  Therefore the ideal
`K_0^sat` generated over all `Theta` is contained in `J direct_sum J`.
The diagonal embedding belongs to the family, and its image of `J`
generates both coordinate ideals: multiplication by `(a,0),(b,0)` and by
`(0,a),(0,b)` separates the two coordinates.  Hence

```text
K_0^sat=J direct_sum J.                                  (2)
```

Every normalized `2`-quasitrace `q` on `D_0` has the form

```text
q=alpha tau_G direct_sum (1-alpha)tau_G,
             0<=alpha<=1,                               (3)
```

because the two units are orthogonal central projections and each nonzero
normalized coordinate restriction is the unique quasitrace on `G`.
Equations `(2)` and `(3)` show that every `q` annihilates `K_0^sat` and that
pullback gives the asserted bijection after quotienting.

Finally,

```text
I_0/K_0^sat
  =(J direct_sum G)/(J direct_sum J)
  ~=G/J=Q.
```

Its II_1-factor trace is a nonzero bounded residual trace.  This is an
abstract countermodel to the sufficiency of the listed structural inputs,
not a counterexample to XCIII: no claim is made that `D_0` is the central
sequence algebra of `C*_r(F_2) tensor Z`.

The Perera--Thiel--Vilalta central-purity theorem applied to the Z-stable
algebra `Z` makes `G=F(Z)` pure.  Since
`Cu(G direct_sum G)=Cu(G) direct_sum Cu(G)`, almost unperforation and almost
divisibility pass coordinatewise to `D_0`.  Thus the model also retains
central pureness; strict comparison does not remove its residual trace.
