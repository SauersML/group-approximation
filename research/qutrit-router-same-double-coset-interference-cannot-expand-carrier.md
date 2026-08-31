---
rg: 2
id: qutrit-router-same-double-coset-interference-cannot-expand-carrier
kind: claim
title: Same-double-coset interference cannot enlarge the qutrit router carrier
artifacts:
  - research/qutrit-router-double-coset-scalar-proof.md
distinct_from:
  qutrit-external-cyclic-router-selects-only-one-hidden-third: that constructs the finite two-to-one star and identifies its hidden source atom; this excludes coherent sums of arbitrarily many translates inside the same qutrit double coset.
  qutrit-two-to-one-phase-graph-requires-central-line-twist: that classifies zero patterns of one group element; this treats analytic linear combinations and their polar supports.
---

Let `C` be the qutrit phase group, let `p_a` be its character
idempotents, and let `U` be the external cyclic router. For arbitrary
coefficients `lambda_i in C` and elements `l_i,r_i in C`, put

```text
X=sum_i lambda_i l_i U r_i.
```

Then every phase block is a scalar multiple of the corresponding router
block:

```text
p_b X p_a=alpha_(b,a) p_b U p_a,
alpha_(b,a)=sum_i lambda_i chi_b(l_i)chi_a(r_i).         (QDS1)
```

Consequently `p_bXp_a=0` for every `b!=2`. For `b=2`, a
nonzero block has exactly the same initial and final support projections as
`Y_a=p_2Up_a`. Its polar is a scalar phase times the polar of `Y_a`.

Thus interference among any number of left-right `C` translates can
delete chosen phase blocks or change their amplitudes, but it cannot add
another hidden `w`-phase to a surviving source. After coupling to the D8
polar,

```text
||(polar(p_2Xp_a)) V_eta||_2^2=1/864
```

for every surviving `a`. The selected pair therefore still occupies at
most `2/864=1/432`, one third of its raw mass.

In particular, the shortest two-coset ansatz
`U+lambda lUr` cannot repair the hidden-third loss. A genuine
interference continuation must use group elements from distinct
`C`-double cosets with different initial `E`-character atoms, not merely
different representatives or phases of the same double coset.
