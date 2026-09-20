---
rg: 2
id: radical-calculus-misses-virtually-torsion-free-groups
kind: claim
title: The full MF-radical calculus, torsion conclusions and finite-index trace together, never puts a nontrivial element into the radical of a virtually torsion-free group
distinct_from:
  torsion-free-seeds-need-kernel-descent-or-trace-corner: that builds one countermodel missing (I) and one missing (C), and concludes a derivation must use both; this builds one countermodel satisfying all of (F), (S), (X), (D), (I), (C) and (A) at once, so using both is still not enough.
  virtually-torsion-free-mf-radical-is-torsion-free: that is the single-host fact that a torsion conclusion and the trace cannot meet in one virtually torsion-free host; this closes every multi-host derivation, through functoriality, saturation, extensions, colimits and descent.
  full-mf-radical-abelianized-cover-is-not-mf: that is a descent across a kernel not known to be radical, which lies outside the calculus; this shows such a step, or an analytic theorem, is unavoidable.
artifacts:
  - research/torsion-free-seeds-need-kernel-descent-or-trace-corner.md
  - research/virtually-torsion-free-mf-radical-is-torsion-free.md
---

**ESTABLISHED (class obstruction), NO PROPERTY `(T)`.**  Use the rules
(F), (S), (X), (D), (I), (C) and input (A) exactly as defined in
`torsion-free-seeds-need-kernel-descent-or-trace-corner`.  There, `T(M)` is
the kernel of the universal torsion-free quotient of `M`.  Define
`U(H) = intersection over N normal of finite index in H of T(N)` and set

```text
Rad^nat(H) = Rad_MF(H) intersect U(H).
```

**Theorem.**

1. `Rad^nat` satisfies (F), (S), (X), (D), (I), every sound instance of (C),
   and (A).  The bare assignment `U` satisfies (A) unconditionally.
2. `Rad^nat(H) = 1` for every virtually torsion-free `H`, in particular for
   every torsion-free group.
3. The countermodels are nested: `Rad* <= Rad^nat <= Rad#`.

**Consequences.**

1. No derivation inside the calculus proves `1 != x in R(H)` for a virtually
   torsion-free `H`.  This holds even if the derivation starts from
   endpoint 2 (A) and uses any torsion-corner theorem.  Consequence 3 of
   `torsion-free-seeds-need-kernel-descent-or-trace-corner` ("use both (C)
   and (I)") is necessary but not sufficient.  The (C)+(I) gate is closed.
2. So every proof of `property-t-free-torsion-free-fp-non-mf-seed` from the
   Leavitt collapse must contain a step outside the calculus.  Either it is
   a radical descent across a kernel not known to be radical, as in
   `full-mf-radical-abelianized-cover-is-not-mf`, or it is an analytic
   non-MF theorem for a specific torsion-free or virtually torsion-free
   group, as in the intrinsic Higman seed route.
3. The torsion-free half of the manuscript therefore has exactly two live
   kinds of route: DF-type descent, and intrinsic seeds.  Every route that
   builds a torsion radical and then passes to a finite-index subgroup,
   directly or after pushing forward, is dead at the invariant `U`.

**Invariant and death step.**  The invariant is `U(H)`, the part of `H` that
dies in every torsion-free quotient of every finite-index normal subgroup.
Every derivation dies at the first virtually torsion-free group it reaches,
where `U = T(Core_H(E)) = 1`.
