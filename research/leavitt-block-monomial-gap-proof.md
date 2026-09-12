---
rg: 2
id: leavitt-block-monomial-gap-proof
kind: route
title: Project fibre permutations and decompose bounded internal coefficient algebras
target: leavitt-regular-atlas-block-monomial-gap
requires:
  - leavitt-regular-atlas-permutation-cover-impossible
  - atlas-defect-gap-limit
---

Projection `W_k -> Sym(A_8)` is a homomorphism. Both atlas charts project to
the regular `A_8` action and a permutation conjugate of it. If every
`s in bar S` projected trivially, the projected atlas would be a nontrivial
finite permutation representation of `U_Q`, impossible by
`leavitt-regular-atlas-permutation-cover-impossible` (or already by minimal
almost periodicity). Hence some relator moves at least two of the `20160`
blocks. A block-monomial unitary moving a proportion `h` of the blocks has

```text
||V-1||_2^2 >= 2h.
```

Taking `h>=2/20160` proves `(BMG1)`.

For the Lipschitz statement, telescope each fixed relator word. A letter
from the conjugated second chart changes by at most `2||U-V||_2`; since
`bar S` is finite, one may take `L=2 max_s q_s`, where `q_s` is the number of
second-chart letters in `s`.

For `(BMG2)`, conjugate the finite-dimensional coefficient algebra into

```text
D(U)=direct_sum_j (M_(r_j) tensor I_(ell_j)).
```

The relative unitary and its atlas model decompose as
`direct_sum_j(U_j tensor I_(ell_j))`, with `U_j in U(n r_j)`. Averaging the
squared defects over `bar S` and over the direct summands gives

```text
average_s ||pi_U(s)-1||_2^2
  = sum_j (r_j ell_j/k) average_s ||pi_(U_j)(s)-1||_2^2.
```

At each fixed `r`, compactness and the absence of a nontrivial exact
finite-dimensional atlas representation give a strictly positive minimum
`E_r`. Put `e_R=min_(1<=r<=R) E_r>0` and retain only summands with `r_j<=R`.
The displayed identity yields `(BMG2)`, since the maximum defect dominates
the average. This proof is independent of `k` and permits arbitrary
multiplicities `ell_j`.

For `(BMG3)`, apply Glebsky's dimension-free normalized-HS simultaneous
almost-commuting theorem to the fixed family of real and imaginary block
coefficients. If `c(U_k)->0`, these coefficients are HS-close to one commuting
family. Assemble the commuting approximants into a block matrix and take its
polar part inside the resulting abelian coefficient algebra. This produces
`V_k` in the `R=1` stratum with `||U_k-V_k||_2->0`. The uniform word-Lipschitz
estimate then transfers `F_k(U_k)->0` to `F_k(V_k)->0`, contradicting `(BMG2)`
at `R=1`. Compactness of the error modulus supplies a fixed positive `c_0`.
