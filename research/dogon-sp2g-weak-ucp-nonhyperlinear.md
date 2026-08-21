---
rg: 2
id: dogon-sp2g-weak-ucp-nonhyperlinear
kind: claim
title: Weak ucp-stability of the symplectic lattice makes the Deligne universal-cover lattice non-hyperlinear
distinct_from:
  hs-stability-forces-nonhyperlinear-central-extension: that is Dogon--Vigdorovich Theorem 1.1, consuming flexible HS-stability of a (T;FD) group to kill a FINITE central extension; this is Dogon's earlier Corollary 1.9, consuming the formally weaker weak ucp-stability of the Kazhdan lattice Sp_2g(Z) to kill the infinite cyclic Deligne extension itself.
  deligne-triple-cover-fd-central-invisibility: that is the finite-dimensional invisibility of the central mark in Deligne's triple cover of Sp_4(Z), an unconditional ingredient of the direct HS-collapse lane; this is the conditional theorem that a stability property of the base lattice already forces non-hyperlinearity of the cover.
  sl3-z-weakly-ucp-stable: that hypothesis concerns SL_3(Z) and is consumed through a thin co-dense HNN pair; this concerns Sp_2g(Z) and is consumed through Deligne's central extension with no auxiliary construction.
---

**THEOREM (Dogon arXiv:2211.10492v3, Corollary 1.9 with its standing
example; read at source).**  Let `g >= 2`, `Gamma = Sp_(2g)(Z)`, and let

```text
1 --> Z --> Gamma~ --> Gamma --> 1                                  (DS1)
```

be the pullback of `Gamma` under the universal cover
`Sp~_(2g)(R) ->> Sp_(2g)(R)` (`pi_1(Sp_(2g)(R)) = Z`).  If `Gamma` is
weakly ucp-stable, then `Gamma~` is not hyperlinear.

Dogon's Corollary 1.9 is stated for any connected semisimple Lie group
with infinite cyclic fundamental group and property (T); the symplectic
case is his "concrete case to keep in mind".  `Gamma~` is Deligne's
non-residually-finite lattice, so a positive answer produces a
finitely generated (indeed lattice) non-hyperlinear group outright.

**Interaction with the lifting square.**  By
`llp-implies-weak-ucp-stability`, the hypothesis follows from the LLP of
`C^*(Sp_(2g)(Z))` (`sp2g-z-full-c-star-algebra-has-llp`), which
Fournier-Facio--Willett record as open for higher-rank arithmetic groups.
This is the residually-finite corner of the same square whose
non-residually-finite corner is
`llp-non-rf-kazhdan-group-is-non-hyperlinear`: there the witness is the
group itself, here it is Deligne's extension; both need only a lifting
property, not a stability theorem.  By
`kazhdan-weak-ucp-stability-is-flexible-stability` the hypothesis is also
exactly flexible HS-stability of `Sp_(2g)(Z)` on hyperlinear
approximations, the form in which Dogon's abstract states it.
