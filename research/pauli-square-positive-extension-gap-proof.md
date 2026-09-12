---
rg: 2
id: pauli-square-positive-extension-gap-proof
kind: route
title: Measure the translated-row gap on the Pauli square
target: finite-nuclear-quotient-does-not-complete-partial-toeplitz-data
requires:
  - finite-positive-definite-window-is-a-relative-corner-selector
---

Write `c=ab`, so the Cayley graph of `G=C2 x C2` with difference set

```text
Delta={1,a,b}
```

is a four-cycle. Every subset `Sigma subset G` satisfying
`Sigma^(-1) Sigma subset Delta` has at most two elements: any three
vertices of a four-cycle contain an opposite pair, whose difference is
`c`, which is not in `Delta`.

For a permitted two-point set, the partial Toeplitz matrix furnished by
(FNQ1) is, up to interchanging the points,

```text
[[I,U],[U,I]] = column(I,U) row(I,U) >= 0,              (PS1)
```

where `U=X` or `U=Z`, and `U=U*=U^(-1)`. Singletons are immediate.
This proves positive definiteness on `Delta`.

Now let `F:G -> M_2` be a full normalized positive-definite function.
It induces a ucp map

```text
Theta:C*(G) -> M_2,             Theta(u_g)=F(g).
```

Choose a Stinespring representation

```text
Theta(y)=W* pi(y) W
```

with `W:C^2 -> K` an isometry. Set

```text
P=WW*,  R=pi(a),  S=pi(b),  A=W*RW,  B=W*SW.           (PS2)
```

The unitaries `R,S` commute. For rectangular operators out of `C^2`,
use the normalized Hilbert--Schmidt norm

```text
||T||_(2,2)^2 = Tr(T*T)/2.
```

Define the two leakage terms

```text
alpha=||(1-P)RW||_(2,2),       beta=||(1-P)SW||_(2,2).
```

Compression gives the exact identities

```text
alpha^2=1-||A||_(2,2)^2,       beta^2=1-||B||_(2,2)^2. (PS3)
```

If

```text
||A-X||_(2,2)<=eta,            ||B-Z||_(2,2)<=eta,
```

and `eta<1`, the reverse triangle inequality in (PS3) yields

```text
alpha,beta <= sqrt(2 eta-eta^2) <= sqrt(2 eta).         (PS4)
```

Because `RS=SR`,

```text
||AB-BA||_(2,2)
 <= ||W*R(1-P)SW||_(2,2) + ||W*S(1-P)RW||_(2,2)
 <= alpha+beta
 <= 2 sqrt(2 eta).                                     (PS5)
```

Both `A` and `B` are contractions. Hence

```text
||XZ-AB||_(2,2)<=2 eta,        ||BA-ZX||_(2,2)<=2 eta. (PS6)
```

The Pauli matrices anticommute, so `||XZ-ZX||_(2,2)=2`. Combining
(PS5)--(PS6) gives

```text
2 <= 4 eta + 2 sqrt(2 eta).                             (PS7)
```

Put `y=sqrt(2 eta)`. Equation (PS7) says `y^2+y-1>=0`, and therefore

```text
eta >= ((sqrt(5)-1)/2)^2 / 2 = (3-sqrt(5))/4.          (PS8)
```

If `eta>=1`, (PS8) is automatic, so the bound holds without a
restriction on `eta`.

At `eta=0` there is also a one-line multiplicative-domain proof:
`Theta(u_a)=X` and `Theta(u_b)=Z` are unitaries, so `u_a,u_b`
belong to the multiplicative domain. The relation `u_a u_b=u_b u_a`
would imply `XZ=ZX`, contradicting `XZ=-ZX`.

The estimate shows exactly where the missing translated rows enter.
Facewise positivity sees the two edges separately. A full group table
places both directions in one Stinespring representation; the commuting
square then forces their compressions to approximately commute, with the
only possible error paid by leakage. Near-unitarity makes that leakage
small, while the Pauli commutator remains of normalized-HS norm two.

Thus even the strongest standard approximation properties of the finite
target algebra cannot manufacture the full table from the partial data.
They become usable only after complete positivity on the concrete Fourier
operator system -- equivalently the missing cross-difference/translated-row
compatibility -- has already been proved.
