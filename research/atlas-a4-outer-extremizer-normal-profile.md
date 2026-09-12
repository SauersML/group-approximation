---
rg: 2
id: atlas-a4-outer-extremizer-normal-profile
kind: claim
title: Every outer twenty-one-quarters extremizer has normal collision lengths four and two
artifacts:
  - experiments/atlas_a4_outer_extremizer_structure.py
  - experiments/atlas-a4-outer-extremizer-structure.json
distinct_from:
  atlas-a4-classical-two-holonomy-profile: that proves the sharp branchwise character inequalities; this identifies the exact finite-group structure of the ten outer equality cases.
---

In the notation of `atlas-a4-classical-two-holonomy-profile`, consider the ten
outer packet alignments attaining

```text
15 E_2HOL=84,                    15 ||q_19243-1||_2^2=16.
```

For every one of the ten, the collision value `q=q_19243` is an involution
whose conjugacy class in `A8=GL_4(F2)` has size `105`.  If

```text
gamma_c=theta(c)c^-1,           gamma_a=theta(a)a^-1,
```

then the following assertions hold at every extremizer:

```text
15 ||gamma_c-1||_2^2=30,        15 ||gamma_a-1||_2^2=24,
ell_q(gamma_c)=4,               ell_q(gamma_a)=2,
<q,gamma_c,gamma_a>=A8.                                  (OUTER-NORMAL)
```

Here `ell_q(v)` is the least number of conjugates of `q` whose product is
`v`.  Thus `gamma_c` fixes no nonzero vector in the natural 15-point action,
whereas `gamma_a` fixes exactly three.  The displayed lengths are minimal:
the exact audit constructs the full 105-element conjugacy class, exhausts all
products of at most three class elements before testing products of two
two-letter products, and finds lengths four and two respectively.  A Cayley
enumeration verifies that the three displayed elements generate all `20160`
elements of `A8`.

Consequently the outer loss from `5` to `21/4` is not a rounding accident.
At every equality case a transvection-valued collision coexists with a
fixed-point-free cross-component cocycle lying four normal steps away.  Any
amplification-stable compiler based on normal generation must therefore pay
for the component-root transport explicitly; the collision readout alone
does not identify it in one, two, or three normal steps.
