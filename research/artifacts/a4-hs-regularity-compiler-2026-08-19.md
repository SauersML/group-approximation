# Robust Hilbert--Schmidt compiler for the atlas A4 triangles

**Date:** 2026-08-19  
**Status:** proved modulo the published finite-group stability theorem of Gowers--Hatami; the remaining atlas problem is overlap compatibility of the resulting regular blocks.

## 1. Statement

Let `d_n -> infinity` and let `A_n,B_n in U(d_n)` satisfy

```text
A_n^3 = 1,
B_n^2 = 1,
||(B_n A_n)^3-1||_(2,d_n) -> 0,
tr_(d_n)(A_n) -> 0,
tr_(d_n)(B_n) -> 0,
tr_(d_n)(B_n A_n) -> 0.
```

Then, after changing only `o(d_n)` dimensions in the flexible normalized-HS sense, the pair is asymptotic to an exact representation of

```text
<A,B | A^3=B^2=(BA)^3=1> ~= A4
```

whose non-regular part has dimension `o(d_n)`.  Equivalently, the exactified representation contains

```text
t_n * Reg(A4)
```

with

```text
12 t_n = d_n-o(d_n).
```

The constants needed for a quantitative version depend only on the fixed group `A4`, never on `d_n`.

## 2. From one relator to a near representation of the whole finite group

Fix once and for all a reduced word `w_g(A,B)` for every `g in A4`.  Define

```text
f_n(g)=w_g(A_n,B_n).
```

Because `A^3`, `B^2` and `(BA)^3` present the finite group `A4`, every multiplication identity

```text
w_g w_h = w_(gh)
```

has a fixed derivation from these three relators.  There are only `12^2` such identities, so the maximum number `L` of uses of `(BA)^3` in the chosen derivations is finite.  Telescoping in the bi-invariant normalized Hilbert--Schmidt metric gives

```text
max_(g,h in A4) ||f_n(gh)-f_n(g)f_n(h)||_2
 <= L ||(B_n A_n)^3-1||_2 -> 0.
```

Thus `f_n` is a genuine dimension-uniform near representation of the **finite group** `A4`; no property-(T), no atlas stability assumption and no growing word window enter here.

## 3. Gowers--Hatami flexible exactification

Gowers and Hatami, *Inverse and stability theorems for approximate representations of finite groups*, arXiv:1510.04085, prove a dimension-independent Hilbert--Schmidt stability theorem for maps from a finite group to unitary matrices.  Their normalization is exactly the normalized Frobenius/Hilbert--Schmidt norm used here.  The key feature is the necessary flexible dimension correction: an `epsilon`-representation in dimension `d` is close to an exact representation in dimension `d+O(epsilon^2 d)`, rather than necessarily in exactly dimension `d`.

Apply their stability theorem to `f_n`.  It gives exact representations

```text
rho_n:A4 -> U(m_n)
```

with

```text
m_n/d_n -> 1
```

and partial-unitary identifications under which the matrices of `rho_n(g)` and `f_n(g)` are `o(1)` apart in normalized HS norm for every fixed `g in A4`.

In particular normalized characters transfer:

```text
chi_n(a)/m_n -> 0,
chi_n(b)/m_n -> 0,
chi_n(ba)/m_n -> 0,
```

where `a,b` are the standard order-three and order-two generators.

## 4. Character-table rigidity leaves only a vanishing residual

Write the irreducible multiplicities of `rho_n` as

```text
m_0,m_1,m_2,m_3
```

for the three one-dimensional irreducibles and the three-dimensional irreducible.  Put `omega=exp(2 pi i/3)`.

On one order-three conjugacy class the character equation is

```text
chi_n(a)=m_0+omega m_1+omega^2 m_2=o(m_n).
```

Taking real and imaginary parts gives

```text
m_0-m_1=o(m_n),
m_0-m_2=o(m_n).
```

On the order-two class,

```text
chi_n(b)=m_0+m_1+m_2-m_3=o(m_n),
```

so, writing `t_n` for any one of `m_0,m_1,m_2` up to `o(m_n)`, one gets

```text
m_0=t_n+o(m_n),
m_1=t_n+o(m_n),
m_2=t_n+o(m_n),
m_3=3t_n+o(m_n).
```

Since

```text
Reg(A4)=1 + chi + chi_bar + 3 rho_3,
```

take

```text
s_n=min(m_0,m_1,m_2,floor(m_3/3)).
```

The direct summand `s_n Reg(A4)` has complement of dimension `o(m_n)=o(d_n)`.  This proves the robust regular-core statement.

The third trace `tr(BA)->0` is not needed after exactification once the chosen standard `ba` lies in an order-three class; it is included because the atlas regular-character microstates provide it automatically and because it makes the local finite-table hypothesis symmetric and directly checkable.

## 5. Consequence for the 30-chart atlas packet

For every pair-cube in `atlas-shortest-a4-triangle-packet`, the two letters already come from exact regular `A8` chart representations.  Hence their individual finite orders and individual regular traces are exact.  Hyperlinear regular-character microstates also make every fixed nonidentity cross word, including `BA`, asymptotically traceless, while the pair-cube relator defect tends to zero.

Therefore **each of the 30 local triangles has a regular A4 core of relative dimension `1-o(1)`**.  There is no remaining local exotic representation type to classify.  The only possible escape is incompatibility of the flexible exactifications on their overlaps: the regular blocks can carry different multiplicity gauges/holonomies around the finite incidence complex.

This is the useful new boundary.  A global proof may now work entirely with regular `A4` inclusion bimodules and their overlap transport, and charge the union of the `o(d)` discarded local complements to a fixed finite number (`30`) of charts.  Thus the total discarded dimension remains `o(d)`.

## 6. Literature source

Primary source used here:

- W. T. Gowers and O. Hatami, *Inverse and stability theorems for approximate representations of finite groups*, arXiv:1510.04085 (v2, 2016), especially the finite-group Hilbert--Schmidt stability theorem in Section 6.  The paper explicitly normalizes Hilbert--Schmidt norm by `d^{-1/2}` and obtains dimension error proportional to `epsilon^2 d`.
