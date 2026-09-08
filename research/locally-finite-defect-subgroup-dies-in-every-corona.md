---
rg: 2
id: locally-finite-defect-subgroup-dies-in-every-corona
kind: claim
title: A locally finite normal subgroup inside the compression defect dies in every norm-corona representation
distinct_from:
  torsion-normal-generator-mf-shadow-equivalence: that assumes the normal closure of the finite-order element contains a finite generating set of the ambient group, so the reblocking argument controls every generator; here the ambient quotient by the locally finite subgroup is nontrivial and no such rewriting exists.
  torsion-normal-generator-has-full-support-corona-core: that produces the uniformly full active core from a finite symmetric generating set expressed in conjugates of the mark; this asks for collapse when the mark generates only a proper normal subgroup.
  binary-jacobson-steinberg-head-root-is-mf-invisible: that is one explicit group and one explicit root; this is the general analytic statement whose specialization would settle it.
artifacts:
  - non_mf_groups_exist.tex
---

**OPEN.**  Let `G` be countable, let `L <= G` have property (T), and let
`u in G` satisfy `uLu^(-1) <= L`.  Let `A` be a locally finite normal
subgroup of `G` with

```text
A <= D_G(L),
```

where `D_G(L)` is the compression defect subgroup.  Prove that every
homomorphism from `G` to an MF group is trivial on `A`.

## What is already available

The Hilbert-Schmidt half is free.  By the transport corollary of
`non_mf_groups_exist.tex` (Corollary 2.5), every operator-norm asymptotic
representation satisfies

```text
||V_n(a)-1||_2 -> 0                      for all a in D_G(L).      (LF1)
```

The missing step is the upgrade of `(LF1)` to triviality in the corona.
Three upgrades are known and none covers this case.

* Property (T) on the normal subgroup (Theorem 2.7 of the manuscript).
  An infinite locally finite group never has property (T).
* A fixed finite-dimensional `rho(L)`-normalized subalgebra
  (`thm:finite-algebra-transport`, the analytic step of the finite-block
  theorem).  In the intended applications the orbit algebras grow: for the
  elementary group of a ring with `ts=1`, conjugating `e_13(1-st)` by
  `EL_3` moves it into ever larger matrix-unit levels, so no single
  finite-dimensional algebra is normalized by the whole of `L`.
* Torsion normal generation (`torsion-normal-generator-mf-shadow-equivalence`).
  That needs the normal closure of the mark to carry a generating set of
  `G`; here `G/A` is nontrivial by design, for instance the symbol quotient
  `EL_n(F_2[z,z^(-1)])` in the Jacobson case.

## Provenance constraint

A cocycle proof of a statement of this shape is known: Eckhardt's
Theorem 4.3 for involutive wreath products rescales a Hilbert-Schmidt
displacement cocycle and applies Delorme-Guichardet.  The manuscript cites
that note and does not use its mechanism, so a route through a rescaled
displacement cocycle is not admissible here; this node asks for an
independent argument.  Recording the constraint so that the method is not
reintroduced by accident.

## Why it is worth proving

With `(LF1)` it would give, for every countable unital ring `R` with
`ts=1` and `q(1-st)=0` for some `q>=1`, that every MF homomorphism of
`EL_n(R)`, `n>=4`, kills the roots with coefficient `1-st`, dropping the
full-idempotent hypothesis `R(1-st)R=R` of the manuscript's ring theorem
in positive characteristic.  It also decomposes
`binary-jacobson-steinberg-head-root-is-mf-invisible`, currently a
frontier hole with no live routes.
