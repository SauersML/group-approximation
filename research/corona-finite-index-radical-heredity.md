---
rg: 2
id: corona-finite-index-radical-heredity
kind: claim
title: The MF radical of a finite-index subgroup is the trace of the ambient radical
distinct_from:
  mf-radical-functoriality: That claim is the one-sided image statement `f(Rad_MF(G)) <= Rad_MF(H)` for an arbitrary homomorphism; this is an equality for a finite-index inclusion, and equality is exactly what functoriality alone does not give.
  corona-hs-radical-is-finite-residual: That computes the 2-norm-invisible set of one concrete group and identifies it with that group's finite residual; this is a general operator-norm formula relating a group to its finite-index subgroups, with no concrete group and no trace in the statement.
  finite-infranormal-subgroup-is-normal: That is an elementary normality fact about finite subgroups, used to rule out a Pauli-packet substitution in the Kun--Thom setting; the only thing it shares with this claim is the phrase "finite index", and it says nothing about any radical.
artifacts:
  - GroupApproximation/Algebra/VisibleQuotient.lean
  - GroupApproximation/Sofic/InducedCoronaMF.lean
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
---

For every finite-index subgroup `H <= G`,

    Rad_MF(H) = H intersect Rad_MF(G).

The inclusion left-to-right is restriction of corona representations; the
inclusion right-to-left is induction of a corona representation of `H` to a
block-monomial corona representation of `G` whose distinguished diagonal block
is the original one.

The same induction is purely algebraic, so it also gives

    Rad_fd(H) = H intersect Rad_fd(G),
    Rad_lin(H) = H intersect Rad_lin(G)

for the finite-dimensional unitary residual and the all-fields linear
residual, while the finite residual obeys the same formula through the
finite-index normal core.
