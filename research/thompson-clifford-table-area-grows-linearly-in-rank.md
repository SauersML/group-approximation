---
rg: 2
id: thompson-clifford-table-area-grows-linearly-in-rank
kind: claim
title: Every full Thompson--Clifford packet table has area linear in its rank
artifacts:
  - research/artifacts/thompson-clifford-central-product-tape-2026-08-20.md
distinct_from:
  finite-mark-centralizer-commutator-area-is-proper: that is a general twisted-Schreier distance estimate for centralizers; this is a crossed-Fox estimate on the lamp quotient and also handles an arbitrarily chosen representative of the identity table entry.
---

**ESTABLISHED.**  Fix any finite presentation

```text
VCl=<S|R>
```

of the Thompson--Clifford central-product tape.  There is a constant
`C_P>0`, depending only on this presentation, such that the following holds.
For `N` distinct sites, let `E_N` be the natural rank-`N` extraspecial Pauli
subgroup and let

```text
sigma_N:E_N -> F(S)
```

be *any* word section of its inclusion in `VCl`.  Then

```text
max_(g,h in E_N)
 Area_R(sigma_N(g) sigma_N(h) sigma_N(gh)^(-1)) >= N/C_P. (TFA1)
```

In particular, changing to longer or noncanonical representatives cannot
make the full multiplication tables have uniformly bounded area.

The coefficient detector is an integral crossed Fox derivative.  Let
`pi:F(S)->V` be the actor quotient and let

```text
M_Z=directSum_X Z
```

with its permutation `V`-action.  The exact quotient

```text
VCl -> (directSum_X F_2^2) semidirect V
```

followed by projection to the `p` coordinate gives a crossed cocycle

```text
d_bar:VCl -> directSum_X F_2.
```

Choose integral finite-support lifts of `d_bar(s)` for `s in S`.  They extend
uniquely to a crossed derivation

```text
D:F(S)->M_Z,
D(uv)=D(u)+pi(u)D(v),
```

whose reduction modulo two is `d_bar`.  Put

```text
C_P=max_(r in R) ||D(r)||_1.                              (TFA2)
```

This maximum is positive: otherwise the estimate below would make `D`
vanish on every null word, contrary to the nonzero derivative of the square
of a `p`-lamp representative.

The integral derivative need not descend to `VCl`.  In the standard
generator-adapted presentation, `D(p^2)=2e_xi`; for an arbitrary
presentation and a word `w_p` representing the base lamp,
`D(w_p^2)=2D(w_p)` and its `xi` coefficient is nonzero.  This is not a
defect in the argument.  It is why `C_P` detects relation cells.  Only
`D mod 2` must descend, and it does so by the displayed lamp quotient.

For every null word `z`, crossed Fox telescoping gives

```text
Area_R(z) >= ||D(z)||_1/C_P.                              (TFA3)
```

To make `(TFA1)` independent of the chosen identity representative, let
`a` be the product of the `N` distinct `p`-lamps, put

```text
u=sigma_N(a),       v=sigma_N(1).
```

Then `pi(u)=pi(v)=1`, `a^2=1`, and reduction modulo two shows
`||D(u)||_1>=N`.  The table cells `(1,1)` and `(a,a)` freely reduce to words
whose derivatives are respectively

```text
D(v),               2D(u)-D(v).
```

The triangle inequality makes at least one of their norms at least
`||D(u)||_1>=N`; `(TFA3)` proves `(TFA1)`.  Thus the tempting one-cell proof
from `D(u^2)=2D(u)` is valid only when `sigma_N(1)` is normalized to the empty
word.  The paired-cell argument is required for arbitrary sections.
