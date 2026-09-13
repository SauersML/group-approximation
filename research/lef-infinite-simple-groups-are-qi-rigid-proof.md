---
rg: 2
id: lef-infinite-simple-groups-are-qi-rigid-proof
kind: route
title: Vershik-Gordon turns finite presentation plus LEF into residual finiteness, which an infinite simple group cannot have, and type F_2 is a quasi-isometry invariant
target: lef-infinite-simple-groups-are-qi-rigid
requires:
  - fp-upgrades-make-non-lef-and-non-lea-cheap
  - un-ladder-rf-rigidity-is-free-mf-rigidity-is-dynamical
artifacts:
  - research/artifacts/un-open-7-coarse-geometry-2026-09-13.md
---

Let `S` be finitely generated, infinite, simple and LEF.

**1. `S` is not finitely presented.** Suppose it were. By
`fp-upgrades-make-non-lef-and-non-lea-cheap`, a finitely presented LEF group is
residually finite (Vershik–Gordon); the argument recorded there is that a local
embedding of a window containing every subword of every relator and one nontrivial
element is multiplicative on that window, hence kills no relator, hence extends to a
genuine homomorphism to a finite group that is nontrivial on the chosen element.
So `S` would be residually finite. But an infinite simple group is not residually
finite: item 3 of `un-ladder-rf-rigidity-is-free-mf-rigidity-is-dynamical`, applied with
the residually finite target `H = S` and the identity homomorphism, forces the identity
to be trivial, which is false for `S ≠ 1`. Contradiction.

**2. `S` is quasi-isometric to no finitely presented group.** For finitely generated
groups with word metrics, being of type `F_2` — equivalently, being finitely presented —
is invariant under quasi-isometry (Alonso; classical, cited not re-read). If `S` were
quasi-isometric to a finitely presented group, `S` would itself be finitely presented,
contradicting step 1.

**3. Not of type `F_2`.** For a finitely generated group, type `F_2` is exactly finite
presentability, so step 1 gives it. A Dehn function is defined relative to a finite
presentation, so `S` has none.

**Model tests.**
- Thompson's group `V` is finitely presented, infinite and simple, so by step 1 it is
  **not** LEF. That is the known conclusion and confirms the direction of the argument.
- A locally finite infinite simple group (for instance the finitary alternating group on
  a countable set) is LEF, infinite and simple, and is indeed not finitely presented.
- A finite simple group is LEF and simple but not infinite; it is finitely presented, so
  the hypothesis "infinite" is load-bearing.
- The free group `F_2` is finitely presented and LEF (being residually finite) but not
  simple; the hypothesis "simple" is load-bearing.
