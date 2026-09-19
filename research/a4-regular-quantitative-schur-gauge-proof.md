---
rg: 2
id: a4-regular-quantitative-schur-gauge-proof
kind: route
title: Average a near intertwiner over A4 and polar-correct inside the commutant
target: a4-regular-quantitative-schur-gauge
requires:
  - a4-coherence-fan-canonically-splits-multiplicity
---

Write `delta_a,delta_b` for the two generator defects and
`eta=delta_a+delta_b`.  Because `A4` is finite, fix once and for all, for every
`g in A4`, a word `w_g(a,b)` representing it, and let

```text
L=max_g |w_g|.
```

Finite-word telescoping gives

```text
||U pi(g)-pi'(g)U||_2 <= L eta                    (1)
```

for every `g`.  Average `U` over the two exact representations:

```text
D=(1/12) sum_(g in A4) pi'(g)^* U pi(g).
```

(Equivalently reverse every `g`; the choice is immaterial.)  The averaging
identity shows that `D` is an exact `A4`-intertwiner.  Every summand is unitary,
so `||D||_op<=1`, while `(1)` gives

```text
||U-D||_2 <= L eta =: delta.                       (2)
```

Since `U` is unitary and `D` is a contraction,

```text
||I-D^*D||_2
 <= ||D^*(U-D)||_2 + ||(D^*-U^*)U||_2
 <= 2 delta.                                        (3)
```

Decompose the two equal regular representations into their identical A4
isotypic blocks.  On each irreducible block an exact intertwiner is `I` on the
irreducible factor tensored with a matrix on the multiplicity factor.  Take the
polar decomposition of each such multiplicity matrix and extend its partial
isometry to a unitary on that multiplicity space.  Because the source and
target regular types are identical, this produces an exact **unitary**
intertwiner `Z`.

All singular values `s` of the contraction `D` lie in `[0,1]`, and
`1-s <= 1-s^2`.  Therefore `(3)` implies

```text
||D-Z||_2 <= ||I-D^*D||_2 <= 2 delta.               (4)
```

Combining `(2)` and `(4)` gives

```text
||U-Z||_2 <= 3 L eta.
```

Thus one may take `C_A4=3L`; no quantity depends on the number of regular
copies.

Finally apply `a4-coherence-fan-canonically-splits-multiplicity` to the
three-dimensional isotypic sector.  In its canonical gauges the A4 action is
the fixed irreducible pair

```text
A=diag(1,omega,omega^2),
B=(2/3)J-I_3
```

tensored with the identity on the multiplicity wire.  Schur's lemma therefore
forces the restriction of the exact intertwiner to be

```text
W' Z W^*=I_3 tensor V
```

for a unitary `V`.  Compression cannot increase Hilbert--Schmidt norm, so the
same estimate, with only the fixed trace normalization of the `3/4` sector,
holds for the compressed near intertwiner.  This proves the claim.