---
rg: 2
id: irs-character-does-not-determine-haar-cylinders
kind: claim
title: Even the complete IRS character does not determine Haar-test joint cylinders
distinct_from:
  manzoor-separation-does-not-specify-haar-cylinders: that shows the published construction supplies only finitely many unspecified one-word marginals; this gives an explicit pair proving that even all one-word marginals would still not recover the IRS cylinder law.
  haar-algebraic-actions-have-permutation-koopman-spectrum: that constrains joint fixed cylinders of a given stabilizer law; this proves those cylinders are invisible to the associated IRS trace in general.
---

There are distinct IRSs `mu,nu` on `S_3` with identical characters

```text
Pr_mu[g in H] = Pr_nu[g in H]       for every g in S_3, (ICD1)
```

but different two-word cylinders.  Explicitly, let `eta_2` be the uniform
measure on the three order-two subgroups and put

```text
mu = (3/4) delta_{ {e} } + (1/4) delta_{S_3},
nu = (3/4) eta_2       + (1/4) delta_{A_3}.             (ICD2)
```

For a transposition `s` and a three-cycle `r`, both characters take value
`1/4` on `s` and on `r` (and value one at the identity), hence agree on all
of `S_3`.  Nevertheless

```text
Pr_mu[s,r in H] = 1/4,
Pr_nu[s,r in H] = 0.                                   (ICD3)
```

Pullback along any surjection `F_2 -> S_3` gives the same phenomenon for IRSs
of a nonabelian free group.

Therefore the GNS trace and algebra used by Manzoor—even if their values on
every group word were known—do not specify the joint stabilizer cylinders
needed for the Haar reciprocal-index test.  Haar-linearity of a particular
IRS realization is extra measure-level data, not an invariant of its IRS
character or GNS algebra.
