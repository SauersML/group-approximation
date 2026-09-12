---
rg: 2
id: three-naive-leavitt-transfers-stop-before-hyperlinearity-proof
kind: route
title: Exhibit the quotient, scalar, and normalized-HS transfer failures
target: three-naive-leavitt-transfers-stop-before-hyperlinearity
requires:
  - leavitt-unit-group-algebra-surjects-onto-leavitt
  - direct-finiteness-not-inherited-by-quotients
  - complex-hyperlinear-leavitt-idempotent-mismatch
  - hs-full-rank-scalar-defect-blocks-naive-rank-decoding
  - normalized-hs-null-loops-erase-determinant-phase
---

For the first failure, the evaluation map `F_2[G] ->> R` is established by
`leavitt-unit-group-algebra-surjects-onto-leavitt`. The free algebra
`k<X,Y>` is a domain and hence directly finite, whereas

```text
k<X,Y>/(XY-1)
```

is not directly finite: `XY=1` but `YX!=1`. Therefore non-direct-finiteness
of the Leavitt quotient cannot be pulled back through evaluation.

For the second failure, write `u=u_g` for the order-three group unit. Over
`C`,

```text
(u+u^2)^2-(u+u^2)=2u^3+(u^4-u)=2I.
```

For approximate models with `||U^3-I||_2 -> 0`, the same expansion gives
`||(U+U^2)^2-(U+U^2)||_2 -> 2`. Over `F_2` the coefficient `2` vanishes.
There is no unital map from a nonzero characteristic-two algebra to a complex
algebra, so this discrepancy cannot be bridged by composing the two
representations. Replacing the element by its complex spectral projection
removes exactly the mod-two evaluation carrying the Leavitt structure.

For the third failure, take nonzero irrational phases `epsilon_d -> 0` and

```text
D_d=(exp(i epsilon_d)-1)I_d.
```

Then `||D_d||_2 -> 0` while `rank(D_d)/d=1`. Direct sums and positive tensor
amplifications retain full-rank scalar defect; its kernel is zero and its
image is the whole space. Separately,

```text
U_d=diag(-1,1,...,1)
```

has `||U_d-I||_2=2/sqrt(d) -> 0` but determinant `-1`, and

```text
ell_d(t)=diag(exp(2 pi i t),1,...,1)
```

is uniformly HS-null with determinant winding one. Its lift to
`{(U,z):z^2=det(U)}` starting at `+1` ends at `-1`. Hence rank and determinant
phase are both invisible to unstructured normalized-HS convergence.

What the terminal Leavitt contradiction needs is different: three coefficient
products acting on one common positive-density coordinate. The established
finite `S_3` transforms compile the literal packet into a system whose desired
columns are `C` and whose nuisance columns are `D`. Elementary linear algebra
shows that a nuisance-annihilating left inverse on all three desired columns
exists exactly when

```text
rank [C D]-rank D=3.
```

This is the remaining assertion of `atlas-hard-packet-s3-channel-decoder`.
If it holds, `finite-window-decoder-from-s3-hard-packet` produces the three
same-coordinate estimates and `leavitt-multiplicative-trace-floor` gives the
dimension-free contradiction. None of the three failed transfers implies
that quotient-rank identity.
