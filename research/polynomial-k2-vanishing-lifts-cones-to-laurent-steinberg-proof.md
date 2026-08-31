---
rg: 2
id: polynomial-k2-vanishing-lifts-cones-to-laurent-steinberg-proof
kind: route
title: Lift both polynomial vertices to the Laurent Steinberg group and expose K2
target: two-coordinate-relators-leave-stable-laurent-k2
requires:
  - one-opposite-steinberg-relator-does-not-close-laurent-cycle
---

For every ring `R` there is a natural exact sequence

```text
1 -> K2(R) -> St(R) -> E_inf(R) -> 1.                         (PKL1)
```

For a finite field `k`, `K2(k)=0`.  Quillen homotopy invariance for
regular rings therefore gives

```text
K2(R_+)=K2(R_-)=K2(R_0)=0.                                   (PKL2)
```

Thus the three Steinberg-to-elementary maps in (PKL1) are isomorphisms for
the two polynomial cone rings and their intersection.

Use their inverses and the ring inclusions into `R_pm` to obtain compatible
homomorphisms

```text
E_inf(R_+) -> St(R_pm),       E_inf(R_-) -> St(R_pm).
```

They agree on `E_inf(R_0)`, so the amalgam universal property gives

```text
Psi:H_inf -> St(R_pm).                                        (PKL3)
```

The Steinberg commutator relations give

```text
[x_12(x_i),x_23(x_i^(-1))]=x_13(1),       i=1,2.
```

Consequently `Psi(w_i)=1` for both coordinate words, and (PKL3) factors as

```text
barPsi:Q_2 -> St(R_pm).                                       (PKL4)
```

This map is surjective.  Indeed, split every Laurent monomial `m` as
`m=m_+m_-` with `m_+ in R_+` and `m_- in R_-`.  For distinct stable
matrix indices `i,j,l`,

```text
[x_(i l)(m_+),x_(l j)(m_-)]=x_(i j)(m).                       (PKL5)
```

Additivity of root groups then handles every Laurent polynomial coefficient,
so all Steinberg generators lie in the image.

Let `p:St(R_pm)->E_inf(R_pm)` be the map in (PKL1).  By construction,

```text
p barPsi=q.                                                    (PKL6)
```

Take any `z in K2(R_pm)=ker(p)`.  Surjectivity of `barPsi` gives
`y in Q_2` with `barPsi(y)=z`.  Equation (PKL6) gives `q(y)=1`.
Therefore restriction of `barPsi` maps `ker(q)` onto `K2(R_pm)`,
proving (TKO2) and noninjectivity of (TKO1).

Finally apply the Bass fundamental theorem twice.  Polynomial variables do
not change K-theory for the regular coefficient field, while two Laurent
variables give

```text
K2(R_pm)
 ~= K2(k) (+) 2 K1(k) (+) K0(k).
```

For finite `k`, the three terms are `0`, `2(k^*)`, and `Z`,
respectively.  This proves (TKO3).  The calculation is stable; no unstable
rank-three identification is used or claimed.

For completeness, the finite-rank assertion uses classical injective
stability, not an identification special to these rings.  If a commutative
noetherian ring `S` has Krull dimension at most `d`, the
Dennis--Vaserstein--van der Kallen--Suslin--Tulenbaev theorem gives

```text
K2(r,S)=ker(St_r(S)->E_r(S)) ~= K2(S),       r>=d+3.           (PKL7)
```

All four rings `R_0,R_+,R_-,R_pm` are noetherian of dimension at most
`d`.  Hence (PKL7) makes the finite-rank Steinberg maps for
`R_0,R_+,R_-` isomorphisms, by (PKL2), and identifies the Laurent kernel
with the group in (TKO3).  Repeat (PKL3)--(PKL6) with `St_r,E_r`.
The factorization (PKL5) only needs a third matrix index, which is available
in the stated range.  Therefore the kernel of the finite-rank map surjects
onto `K2(r,R_pm)~=K2(R_pm)`.

This argument says exactly where stability is used.  Below the range
`r>=d+3`, neither injectivity of stabilization nor the vanishing of the
polynomial vertex kernels follows from (PKL7); no rank-three conclusion is
being imported from stable K-theory.
