---
rg: 2
id: stw61-projective-line-embedding-commutator-proof
kind: route
title: A projective-space test forces a trivial range bundle to meet a tautological line at half overlap
target: stw61-finite-representation-maximal-commutator
requires: []
artifacts:
  - research/artifacts/stw61-projective-finite-representation-obstruction-2026-09-05.md
---

Represent z over CP^(N-1) as i(2e-1), where e is the tautological
rank-one projection, and represent D constantly by rho. Every
conjugate Q=W rho(p) W* has globally trivial range and complement.
The scalar lambda=Tr(eQ) must attain zero: otherwise projection to Q
would embed the tautological line into a trivial rank-r bundle,
contradicting c_r((L*)^(sum r)) != 0. Applying this to the complement
forces lambda to attain one. Connectedness then gives lambda=1/2,
where the commutator norm is 2 sqrt(lambda(1-lambda))=1.

The universal upper bound is one. The artifact also proves the
two-projection coefficient case directly using the central element
(p-q)^2, and checks the ambient free-product inclusion hypotheses.
