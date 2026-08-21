---
rg: 2
id: atlas-a4-classical-two-holonomy-profile
kind: claim
title: The sharp classical two-holonomy constant is five on the inner branch and twenty-one quarters on the outer branch
artifacts:
  - experiments/atlas_a4_classical_two_holonomy_profile.py
  - experiments/atlas-a4-classical-two-holonomy-profile.json
distinct_from:
  atlas-a4-gl5-two-holonomy-readout: that proves the sharp constant five on the 202 exact packet positions in the 31-point GL5(F2) extension; the present claim exhausts the inner and outer automorphism sectors of A8 in its natural 15-point action and exhibits outer positions where five fails.
  atlas-a4-two-holonomy-reflection-energy-ceiling: that asks for an asymptotic dimension-independent estimate for arbitrary amplified regular charts; the present statement is an exact finite classical calibration only.
---

Let `pi_15` be the permutation representation of
`A8=GL_4(F2)` on the fifteen nonzero vectors of `F2^4`.  Evaluate the first
chart identically and the second chart through either

```text
theta_g(x)=g x g^-1
```

or

```text
theta_g^out(x)=g (x^-1)^T g^-1,
```

where `g` runs through `GL_4(F2)`.  Exhaust the `20160` positions in each
branch and retain the positions satisfying all thirty shortest A4 packet
relations exactly.  There are exactly thirty survivors in each branch, as in
`atlas-a4-19243-classical-collapse`, and collision `q=q_19243` is nonidentity
at all sixty survivors.

For a retained position put

```text
c=hk,
a=zb,
E_2HOL=2 ||theta(c)c^-1-1||_2^2+||theta(a)a^-1-1||_2^2,
epsilon_q=||q-1||_2,
```

with normalized Hilbert--Schmidt norm in `pi_15`.  Then the sharp branchwise
inequalities are

```text
E_2HOL <= 5 epsilon_q^2                              (inner),
E_2HOL <= (21/4) epsilon_q^2                         (outer).       (A4-CLASS-2HOL)
```

The inner constant `5` is attained at fourteen positions.  The outer constant
`21/4` is attained at ten positions.  In particular, the coefficient `5`
fails at exactly those ten outer positions: there

```text
15 E_2HOL=84,             15 epsilon_q^2=16.
```

The computation is exact.  A matrix `v` fixes `2^d-1` nonzero vectors when
`d=dim ker(v-1)`, hence

```text
15 ||pi_15(v)-1||_2^2=2(16-2^d).
```

The script performs only arithmetic over `F2`, enumerates both automorphism
cosets, checks the thirty packet words, and tabulates the resulting integer
defect numerators.  No floating-point optimization enters the claim.

This corrects the tempting extrapolation from the 31-point GL5 screen: the
constant five is not even universal across the finite classical A8 sector.
Any amplified proof must either retain the inner/outer distinction or use a
coefficient at least `21/4` before accounting for genuinely matrix-valued
multiplicity holonomy.
