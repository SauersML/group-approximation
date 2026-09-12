---
rg: 2
id: odd-parity-collisions-prove-zero-compression-rigidity
kind: route
title: Use norm derivatives on odd triples and move a path defect beyond the inverse memory
target: unrestricted-zero-compression-feedback-is-surjunctive
requires: []
artifacts:
  - research/artifacts/gottschalk-unrestricted-order-three-odd-parity-obstructions-2026-09-08.md
---

On V=ker E, the block norm N(d)=E(dR_t d) is zero only at the
zero even triple. The identity Q_t(1+d)=1+N(d) removes all
non-norm feedback on this odd-parity subshift. For q satisfying
the claim's criterion, put v=Kq=Aq and d=(1+q)R_t v. Then
N(d+v)+N(d)=q, so 1+d and 1+d+v are distinct inputs with equal
F outputs. Conversely any collision on this subshift yields
exactly such a q.

When EAE=0, the restriction is d -> d+K N(d). Nonzero block
coefficients of K define a transitive directed graph. A shortest
directed cycle provides the required q. If the graph is acyclic
but has an edge, take a shortest path whose initial block cannot
influence the inverse's finite determining set at its endpoint.
Its indicator satisfies the norm-derivative equation except at
the initial block. The two outputs then agree on the determining
set although their inputs differ at the endpoint. Hence K=AE=0.
Two-block elimination with the identity compressed map gives
surjectivity.

For A_4, injectivity forces augmentation zero and therefore
eae is a multiple of the full group norm, where e=1+t+t^2.
The four-coset action is 2-transitive. Equivariance makes every
diagonal coefficient of K zero and, if K is nonzero, every
off-diagonal coefficient nonzero. The indicator of two cosets
then meets the exact collision criterion, so K must vanish.
