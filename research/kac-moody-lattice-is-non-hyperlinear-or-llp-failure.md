---
rg: 2
id: kac-moody-lattice-is-non-hyperlinear-or-llp-failure
kind: claim
title: Every simple Kazhdan Kac-Moody lattice is non-hyperlinear or its full C*-algebra fails the local lifting property
distinct_from:
  llp-non-rf-kazhdan-group-is-non-hyperlinear: that is the general dichotomy for non-residually-finite Kazhdan groups; this instantiates it at the explicit finitely presented simple Kazhdan groups of Caprace--Remy, where the alternative is sharpest because the groups are simple and have no finite-dimensional representations at all.
  simple-kazhdan-kac-moody-lattices-exist: that is the existence of the groups; this is what the programme's theorems say about each of them.
---

**THEOREM.**  Let `Lambda` be any group as in
`simple-kazhdan-kac-moody-lattices-exist` (e.g. `Lambda_(2,4,6)(q)`,
`q > 1764^3`).  Then exactly one of the following holds:

```text
(a) Lambda is not hyperlinear  -- and then it is an explicit finitely
    presented simple non-hyperlinear group, closing the goal;
(b) Lambda is hyperlinear, and then Lambda is NOT weakly ucp-stable, NOT
    flexibly HS-stable on hyperlinear approximations, and C^*(Lambda)
    FAILS Kirchberg's local lifting property.                      (KMD1)
```

In case (b) the failure of LLP is of a new kind: Ioana--Spaas--Wiersma's
failures come from second cohomology of relative-(T) pairs, whereas here
it would come from hyperlinearity of a simple group with no
finite-dimensional representations.  So the Kac--Moody lattices are
"forced witnesses": whichever way the goal falls for them, they are a
counterexample to something.

**Relation to Fournier-Facio--Willett Question 1.9** (arXiv:2603.18456v2:
is there an infinite property (T) group with the (L)LP?).  A Kac--Moody
lattice as above answers it positively exactly in case (a)'s complement
being false: if `C^*(Lambda)` has the LLP then `Lambda` is a simple
finitely presented Kazhdan group with the LLP AND non-hyperlinear; if it
does not, the class of (L)LP failures acquires its first members with no
finite-dimensional representations at all.  Either way the lattice
settles a published question.

**Why the dichotomy is not obviously decidable either way.**  Both sides
are consistent with everything known: no hyperlinearity proof can proceed
through finite quotients or finite-dimensional representations (there are
none), and the only known tool for hyperlinearity of groups without finite
quotients is soficity permanence (amalgams over amenable subgroups, which
Kac--Moody lattices are not: they are amalgams of finite groups of Lie
type along a chamber, `Lambda = *_(chamber) P_J`, a complex of FINITE
groups, and complexes of finite groups over non-tree nerves have no
soficity permanence theorem).  Conversely, no LLP result reaches a
Kazhdan group (`non-rf-kazhdan-group-with-llp-full-c-star-algebra`).
