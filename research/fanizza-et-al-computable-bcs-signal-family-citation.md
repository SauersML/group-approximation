---
rg: 2
id: fanizza-et-al-computable-bcs-signal-family-citation
kind: route
title: Import the computable BCS signal family from Fanizza et al. Definition 4.1 and Theorem 4.4
target: fanizza-et-al-computable-bcs-signal-family
requires: []
---

Literature import, verified 2026-08-20 against arXiv:2510.04943v4,
Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao, *The NPA hierarchy
does not always attain the commuting operator value*.

Definition 4.1 defines an `L`-family exactly by the computability of
`m |-> (B_m,C_m)`, positive tracial signal in the membership case, and the
bound `phi_S(D)<=C_m epsilon` for every epsilon-perfect strategy in the
nonmembership case. Theorem 4.4 states that such a family exists for every RE
set. The proof's final displayed estimate explicitly constructs the integer
`C_m`; no uniformity over `m` is asserted or needed here.

The source theorem applies to arbitrary commuting-operator strategies, hence
also to finite-dimensional and maximally-entangled strategies. This route
imports only the stated family theorem, not the paper's later NPA fixed-point
construction.
