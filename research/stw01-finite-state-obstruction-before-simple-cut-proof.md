---
rg: 2
id: stw01-finite-state-obstruction-before-simple-cut-proof
kind: route
title: Capture absence of traces in finitely many commutators before taking a separable simple subalgebra
target: stw01-traceless-separable-simple-reduction
requires:
  - stw01-separable-simple-reduction
artifacts:
  - research/artifacts/stw01-traceless-simple-reduction-2026-08-30.md
---

Assume Problem I fails.  Use the classical AW*-factor reduction already
isolated in `stw01-separable-simple-reduction-proof`: there is a finite
AW*-factor `M` whose faithful normalized dimension quasitrace `q` is
nonadditive.  Such a factor has no tracial state.  Indeed, its normalized
dimension quasitrace is unique, so a tracial state would equal `q`, contrary
to nonadditivity.  Choose self-adjoint `x,y in M` witnessing the failure of
additivity.

We first capture `T(M)=empty` in a separable subalgebra.  For every pair
`a,b in M`, let

```text
F_(a,b)={phi in S(M):phi(ab-ba)=0}.
```

These are weak-star closed subsets of the compact state space `S(M)`, and

```text
intersection_(a,b in M) F_(a,b)=T(M)=empty.
```

Compactness gives finitely many pairs `(a_i,b_i)` whose corresponding
closed sets already have empty intersection.  Put

```text
C=C*(1,x,y,a_1,b_1,...,a_N,b_N) subset M.
```

Then `C` has no tracial state.  Otherwise a tracial state on `C` extends,
by the positive Hahn--Banach state-extension theorem, to a state `phi` on
`M`; since every selected commutator lies in `C`, that extension belongs to
all the finitely many `F_(a_i,b_i)`, a contradiction.

The finite AW*-factor `M` is simple as a C*-algebra, as proved in
`stw01-separable-simple-reduction-proof`.  Apply the standard recursive
fullness lemma there to place the separable unital algebra `C` in a
separable unital simple subalgebra

```text
C subset B subset M.
```

Any tracial state on `B` would restrict to one on the unital subalgebra
`C`, so `T(B)=empty`.  The restriction `q|B` remains faithful and
nonadditive because `x,y in B`.  Its matrix extension rules out proper
isometries in every matrix algebra over `B`, hence `B` is stably finite.
It is non-elementary, and Haagerup's theorem makes it nonexact.

The converse is immediate: the displayed `B` itself carries a bounded
quasitrace which is not a trace.

