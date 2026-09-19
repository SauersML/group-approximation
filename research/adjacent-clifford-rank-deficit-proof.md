---
rg: 2
id: adjacent-clifford-rank-deficit-proof
kind: route
title: Apply Clifford induction and count the unique target root eigenspace
target: adjacent-clifford-flow-has-one-third-rank-deficit
requires:
  - adjacent-clifford-orbit-transition-graph
---

Consider first a match from upper depth `a` to opposite depth `a+1`.
`adjacent-clifford-orbit-transition-proof` shows that every nonzero target
newest-layer character forced by such a match is

```text
ell_B=(0,1,0).                                          (ARD1)
```

Its orbit is `O_B` of size three.  The stabilizer of `ell_B` modulo two is
the lower point stabilizer, so its full inverse image `I_B` in
`G_(a+1)` is precisely the opposite Iwahori and has index three.  Clifford
theory says every irreducible target over `O_B` is induced from an
irreducible (possibly projective after quotienting the newest layer)
representation `xi` of `I_B` over `ell_B`:

```text
rho=Ind_(I_B)^(G_(a+1)) xi.                             (ARD2)
```

Restriction of `rho` to the normal newest layer is the equal-multiplicity
sum of the three characters in `O_B`.  Hence its `ell_B` eigenspace has
dimension exactly `dim(rho)/3`.  Every lower-to-higher intertwiner lands in
this eigenspace by `(ARD1)`.  Summing over all target irreducibles and all
depths gives

```text
dim(H_up)<= (1/3)dim(Pi_-)=d/3.                         (ARD3)
```

This also proves `(ACF4)--(ACF5)`: Frobenius reciprocity supplies the
induced extension of every participating inertia label, while orbit size
three gives its dimension and the two conjugate-character complements.
The multiplier carried by `xi` changes the label category but not this
physical-rank identity.

For a match from plus depth `a` down to minus depth `a-1`, reverse the two
charts.  The reverse pullback forces the character
`ell_C=(0,0,1)` in the newest layer of the higher plus target.  This is
another point of the same orbit `O_B`, so its eigenspace is again exactly
one third of every participating plus target.  Summing now over `Pi_+`
gives

```text
dim(H_down)<=d/3.                                      (ARD4)
```

The two conductor directions are orthogonal, so `(ARD3)--(ARD4)` prove
`(ACF2)`. Under the additional hypothesis preceding `(ACF3)`, the maximal
exact intertwiner space is exactly the sum of these adjacent blocks and
therefore supports at most `2d/3` of a unitary comparison. Its normalized
Hilbert--Schmidt distance from that space is at least `1/sqrt(3)`; applying
the uniform congruence spectral gap of the fixed Iwahori gives `(ACF3)`.
