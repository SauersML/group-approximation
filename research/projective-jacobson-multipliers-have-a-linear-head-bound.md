---
rg: 2
id: projective-jacobson-multipliers-have-a-linear-head-bound
kind: claim
title: Every projective Jacobson multiplier has a linear head bound
artifacts:
  - research/superperfect-lift-and-abelian-exponent-bound-proof.md
distinct_from:
  binary-gl-finite-sections-have-no-projective-k2-phase: that computes the Schur multiplier of each ambient finite binary general linear group; this works for arbitrary projective sectors and uses superperfectness of the Jacobson group itself.
  scalar-rephased-toeplitz-sections-still-collapse-head: that controls scalar generator rephasings of the natural Toeplitz finite sections; this controls every tuple whose relators are block-central, without a finite-section hypothesis.
  bounded-block-jacobson-microstates-also-collapse: that assumes bounded irreducible block dimension; the present constant is independent of all block dimensions and of the number of sectors.
---

**ESTABLISHED.** Put

```text
G=EL_28(F_2<S,T | TS=1>)
```

and fix a finite presentation `G=<X | R>` and a word representing

```text
w=x_13(1-ST).
```

There is a constant `C_w<infinity), depending only on this fixed
presentation and word, with the following property.

Let `U=(U_x)_(x in X)` be a tuple of finite-dimensional unitaries.
Suppose there is a common reducing decomposition

```text
H=directSum_j H_j
```

such that every relator is scalar on every block:

```text
r(U)|_(H_j)=zeta_(r,j) I_(H_j),      |zeta_(r,j)|=1.
                                                               (PJB1)
```

Then, independently of the total dimension, the block dimensions and
the number of blocks,

```text
||w(U)-I||_2
 <= C_w max_(r in R)||r(U)-I||_2.                       (PJB2)
```

In particular, if all relators tend to the identity in normalized
Hilbert--Schmidt norm, the head tends to the identity. This closes:

* exact projective representations with small relator multipliers;
* arbitrary direct sums of projective sectors with sector-dependent
  multipliers;
* K2 or Schur-multiplier finite-section ansatze whose relation errors
  lie in the represented block center.

The input is structural. The group `G` is superperfect: its rank-28
Steinberg cover is the universal central extension and has zero kernel
over the binary Jacobson ring. Hence every homomorphism
`G->PU(d)` lifts to `U(d)). Every exact finite-dimensional linear
representation kills `w). Perfectness then expresses the exponent
vector of `w` as an integral combination of the relator exponent
vectors, which gives `(PJB2)`.

This is not full head collapse. A general approximate representation
need not make its relators scalar, even approximately in a common
reducing decomposition. The remaining projective-looking escape is
therefore precisely a genuinely noncentral, coherently mixed relator
error.

DERIVATION
superperfect-lift-and-abelian-exponent-bound-proof
