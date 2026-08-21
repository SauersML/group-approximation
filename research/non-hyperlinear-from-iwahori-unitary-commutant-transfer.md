---
rg: 2
id: non-hyperlinear-from-iwahori-unitary-commutant-transfer
kind: route
title: Collapse the HNN commutator using only one-sided Iwahori commutant transfer
target: non-hyperlinear-group
requires:
  - sl2-z-same-dimension-hs-stable
  - iwahori-unitary-commutant-transfer
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Let

```text
A=SL_2(Z[1/2])=C_+ *_(B_+=B_-) C_-,
G=<A,t | [t,C_+]=1>,
w=[t,a],                  a in C_-\B_-.               (IUR1)
```

Britton's lemma gives `w!=1` in `G`.  Suppose `G` were hyperlinear and take
canonical-trace microstates.  By `sl2-z-same-dimension-hs-stable`, round the
restrictions to the two copies of `C=SL_2(Z)` independently to exact
same-dimensional representations `pi_+,pi_-`; the Iwahori edge defect still
tends to zero.  The HNN relators say that `U(t)` almost commutes with the
first vertex, so `iwahori-unitary-commutant-transfer` makes it almost commute
with the second vertex and hence with `pi_-(a)`.  Rounding errors then give

```text
||U(w)-I||_2->0.                                      (IUR2)
```

Canonical microstates for the nontrivial word `w` instead have
`tr(U(w))->0` and `||U(w)-I||_2->sqrt(2)`, a contradiction.  Therefore `G`
is a finitely presented nonhyperlinear group.

The route consumes neither flexible stability of `A` nor the full
Dogon--Vigdorovich Iwahori repair question.  Its sole open analytic input is
the one-sided unitary inequality `(IUCT2)`.
