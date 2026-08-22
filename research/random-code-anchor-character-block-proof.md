---
rg: 2
id: random-code-anchor-character-block-proof
kind: route
title: Diagonalize coordinate conjugations and round one reflected anchor
target: random-code-anchor-pinchings-contract-exact-transverse-energy
requires: []
---

Use the joint code-character PVM to decompose `L_2(M)` into the orthogonal
blocks `p_x L_2(M) p_y`.  Coordinate pinching has the scalar multiplier
`1_(x_a=y_a)` on such a block.  Off the common commutant, `x+y` is a
nonzero codeword, so uniform coordinate averaging removes at least its
relative-distance fraction.  Independent pinching compositions multiply
the survival probabilities.

For the nonlinear realization, pinching a reflection `B` by the involution
`A` is the `L_2` orthogonal projection `X` onto `{A}'`.  The pinching
disturbance is exactly one quarter of `||[A,B]||_2^2`.  Spectral sign inside
`{A}'` moves `X` by at most the same squared amount, and diagonal/off-diagonal
orthogonality adds the two costs.  This proves the claimed one-half bound.
