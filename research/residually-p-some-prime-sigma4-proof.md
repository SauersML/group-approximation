---
rg: 2
id: residually-p-some-prime-sigma4-proof
kind: route
title: Uniform factorial thresholds make every diagonal sequence converge to one, so only the prescribed prime sees a defect
target: residually-p-for-some-prime-is-sigma4-complete
requires:
  - residually-p-two-generator-recursive-is-pi3-complete
  - index-set-profinitely-closed-is-pi3-complete
---

Write `J = J_e` and `J^s = J u (-J) u {0}`; all rows are positive, and
`0, 1 in J`.

**Only `1` and the elements themselves are pro-`q` limit points, for `q`
not dividing any row's base.**  Fix `q` and `m`.  By the two computations
in the claim body, all but finitely many elements of `J` are `= 1` in
`Z/q^m`.  Let `x` be an integer with `(x + q^m Z) n J != empty` for every
`m`, and choose witnesses `u_m in J`.  If infinitely many `u_m` are
distinct, then for each fixed `m_0` all but finitely many of them are
`= 1` modulo `q^{m_0}`, while each is `= x` modulo `q^{m}` for `m >= m_0`;
hence `x = 1` modulo `q^{m_0}` for every `m_0`, so `x - 1` is divisible by
every power of `q` and `x = 1 in J`.  Otherwise some `u` repeats
infinitely often and `x = u in J`.  So `J` is pro-`q` closed.

**The prescribed prime sees exactly the infinite rows.**  Fix `p`, and let
`row(i, infinity)` be an infinite row over `p`.  Since `p^(n!) = 0` in
`Z/p^m` as soon as `n! >= m`, the row converges `p`-adically to its shift
`c_i`, which is not in `J` by construction; so `J` is not pro-`p` closed.
Conversely, if every row over `p` is finite, then, as above, all but
finitely many elements of `J` are `= 1` modulo `p^m` (rows over other
primes and their shifts), while the finitely many elements of the finite
`p`-rows are themselves in `J`, so the same dichotomy gives that every
pro-`p` limit point lies in `J u {0, 1} = J`.  This is (S4a); the
symmetrization `J^s` changes nothing, because negatives of the rows
converge to the negatives of the same limits, which are again `-1`, `0`,
or elements of `J^s`.

**Assembly.**  `FIN` is uniformly `Sigma^0_2`-complete, so the `i`-th row
can be made infinite exactly when a prescribed `Sigma^0_2` event holds;
grouping the rows by prime, "all rows over `p` are finite" realizes an
arbitrary `Pi^0_3` condition of `p`, uniformly.  Hence "some prime `p` has
all its rows finite", i.e. "`J` is pro-`p` closed for some `p`", i.e.
"`G_J` is residually a finite `p`-group for some `p`", is
`Sigma^0_4`-hard; with the upper bound it is `Sigma^0_4`-complete.
