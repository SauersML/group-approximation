---
rg: 2
id: leavitt-prefix-boundaries-do-not-split-additive-character-mass
kind: claim
title: One additive root character can detect every binary Leavitt prefix boundary
distinct_from:
  toeplitz-defect-idempotents-do-not-localize-root-characters: that treats pairwise orthogonal Toeplitz idempotents; this treats the exponentially branching pure Leavitt prefixes which produce the Heisenberg packet.
  relative-leavitt-active-subspaces-expand-by-two: that proves the coefficient subspaces double; this proves that their dual additive-character carriers need not split at all.
  leavitt-prefixes-form-exponential-heisenberg-packet: that uses all prefix partners to force tensor-product dimension pressure; this shows why the same packet does not by itself give a sum of disjoint marked masses.
---

In the relative binary Leavitt envelope `R=L_A(S)`, the family of pure prefix
coefficients

```text
{s_alpha:alpha a finite binary word}                     (LPB1)
```

is `k`-linearly independent.  Hence there is an additive character

```text
chi:(R,+)->mu_p                                          (LPB2)
```

which is nontrivial on `s_alpha` for every binary word `alpha`.  The same
statement holds for all pure `t_alpha`.

At one fixed depth, independence follows immediately from

```text
t_alpha s_beta=delta_(alpha,beta)A.                      (LPB3)
```

Across different depths, the relative Leavitt presentation is graded by
`deg(s_i)=1`, `deg(t_i)=-1`, and `deg(S)=0`, so a linear relation separates
by word length; `(LPB3)` then kills every coefficient.  Define an
`F_p`-linear functional to take value one on every vector in `(LPB1)`, extend
it to the additive vector space of `R`, and compose with a fixed nontrivial
additive character of `F_p`.

Consequently the coefficient doubling

```text
V -> s_0V direct_sum s_1V
```

does not make additive-root Fourier mass branch into disjoint spectral
layers.  A single character fiber can detect every new prefix at every depth.
The exponentially many Weyl partners in
`leavitt-prefixes-form-exponential-heisenberg-packet` turn this into growing
tensor dimension, but hyperlinearity permits that dimension growth.

Therefore the boundary payment sought in
`affine-leavitt-boundary-shear-payment` cannot be a first-detection argument
on one root coordinate.  It must use correlations between paired root
coordinates (a Gram/range inequality), or a non-additive finite packet cut
which forces different prefixes onto genuinely orthogonal carriers.
