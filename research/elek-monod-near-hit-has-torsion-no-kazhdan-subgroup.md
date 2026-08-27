---
rg: 2
id: elek-monod-near-hit-has-torsion-no-kazhdan-subgroup
kind: claim
title: The Elek--Monod dynamical alternating near-hit has 3-torsion and its full group has no infinite Kazhdan subgroup
distinct_from:
  simple-sofic-total-mf-radical: That is an existential countable simple sofic full-MF-radical group obtained from the Clifford witness; this is a concrete finitely generated dynamical simple sofic group and records two rigorous reasons it cannot supply a torsion-free Kazhdan kernel.
  elek-szabo-envelope-loses-torsion-free-kazhdan-control: That concerns the uncountable universal simple sofic envelope and a countable descent with no torsion or Kazhdan control; this concerns a finitely generated dynamical alternating group and proves actual torsion and property-(T) exclusions.
  titz-witzel-simple-kazhdan-cat0-lattices-exist: Those groups are finitely presented, torsion-free, simple and Kazhdan, with soficity not established in the cited source; the dynamical group supplies the complementary simple-sofic properties but fails torsion-freeness and property (T).
artifacts:
  - research/torsion-free-sofic-exact-mf-radical-over-z.md
---

For the free minimal expansive Cantor `Z^2`-action `Z^2 actson X`
constructed by Elek--Monod, let

```text
A = A(Z^2, X) <= [[Z^2 actson X]]
```

be its dynamical alternating group.  Then

```text
A is finitely generated, infinite, simple, nonamenable and sofic,
A has no nontrivial finite quotient,
A contains a nontrivial element of order 3.                    (EM1)
```

Moreover

```text
[[Z^2 actson X]] contains no infinite countable property-(T) subgroup,
A is inner amenable and does not have property (T).             (EM2)
```

Thus this is a strong concrete near-hit for the kernel sought by
`torsion-free-sofic-exact-mf-radical-over-z`: finite generation, simple
soficity and absence of finite quotients are already present.  It cannot be
used as that kernel, nor can an infinite Kazhdan subgroup be extracted from
its ambient topological full group, because `(EM1)` gives genuine torsion and
`(EM2)` excludes every infinite property-`(T)` subgroup of the full group.

The primary-source boundary remains open on the complementary side.
Alekseev--Thom, arXiv:2608.05362 (2026-08-05), Open Problem 6.1, explicitly
ask whether a finitely presented sofic property-`(T)` group which is not
residually finite exists.  Titz Mite--Witzel, arXiv:2509.05054v2
(2026-08-20), Corollary B, supply finitely presented torsion-free simple
property-`(T)` CAT(0) groups, but that paper makes no soficity claim.  Hence
the cited primary sources provide the two complementary near-hits, not the
torsion-free sofic Kazhdan seed required by the target.
