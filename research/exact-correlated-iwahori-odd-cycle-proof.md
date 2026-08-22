---
rg: 2
id: exact-correlated-iwahori-odd-cycle-proof
kind: route
title: Eliminate the modular three-cycle and iterate the parabolic square statistic
target: exact-correlated-iwahori-dessins-have-odd-parabolic-cycles
requires: []
---

Write a modular dessin as `(a,b)` with `a^2=b^3=1` and put `u=ab`.
The edge involution is

```text
e=ab^2aba=u a u^2 a.                                  (ECD1)
```

Therefore

```text
alpha(u)=u^(-1)e=a u^2 a,                             (ECD2)
```

so the parabolic of the Nielsen-twisted restriction is conjugate to the
square of the original parabolic.  Applying `(ECD2)` to the two extendible
dessins in an exact Nielsen matching gives

```text
u_0 conjugate u_1^2,          u_1 conjugate u_0^2,
```

and hence `u_0` is conjugate to `u_0^4` (and similarly for `u_1`).

If a finite permutation `u` has an even cycle, choose a cycle whose length
has maximal positive 2-adic valuation `r`.  Under fourth power, a cycle of
2-adic valuation `r+2` is the only possible source of cycles with valuation
`r`; cycles of valuation `r` themselves split to valuation `r-2` (or to odd
cycles when `r<=2`).  Maximality says that no source of valuation `r+2`
exists, whereas `u` has a cycle of valuation `r`.  Thus `u` and `u^4`
cannot have the same cycle type.  All cycles are odd.

For the bounded-cycle asymptotic statement, changing `delta n` permutation
arrows affects at most `O(L delta n)` points in cycles of length at most
`L`.  Delete those affected cycles from both near-conjugacies and apply the
exact maximal-valuation argument on the common remainder.  The even-cycle
mass is `O(L delta)`.

