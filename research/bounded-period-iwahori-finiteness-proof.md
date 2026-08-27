---
rg: 2
id: bounded-period-iwahori-finiteness-proof
kind: route
title: Kill a unipotent power and invoke the S-arithmetic normal-subgroup theorem
target: bounded-period-iwahori-quotients-are-finite
requires:
  - iwahori-square-root-presentation-is-bs14-plus-one-involution
  - sl2-s-arithmetic-noncentral-normal-subgroups-have-finite-index
---

In `(BPI1)`, `s` is a nontrivial unipotent and has infinite order.  Hence
`s^N` is nontrivial and noncentral for every `N>=1`.  By
`sl2-s-arithmetic-noncentral-normal-subgroups-have-finite-index`, its normal
closure has finite index in `Gamma`.  Therefore

```text
Gamma/<<s^N>>
```

is finite.  The group `(BPI2)` is a further quotient, so it is finite as
well.

For completeness, fix one finite presentation of `Gamma_(L,N)`.  Choose a
word representative for each group element.  Since the group is finite,
the finitely many multiplication-table words have a finite maximum filling
area in this presentation.  A generator tuple with presentation defect
`delta` therefore induces an approximate representation of the entire
finite multiplication table with defect `O_(L,N)(delta)`.  Finite-group
Hilbert--Schmidt stability (equivalently the Gowers--Hatami correction
theorem, allowing negligible dimension adjustment) gives a genuine
representation at distance

```text
f_(L,N)(delta) ->0                 as delta->0.        (BPF1)
```

This proves fixed-level flexible stability.  The constants obtained by this
argument depend on the finite quotient and its chosen fillings; no uniform
lower bound in `L,N` is asserted.
