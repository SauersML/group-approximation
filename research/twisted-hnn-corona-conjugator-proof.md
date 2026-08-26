---
rg: 2
id: twisted-hnn-corona-conjugator-proof
kind: route
title: Corner the universal HNN into an amalgam, apply Shulman, and inject the group by its regular trace
target: twisted-hnn-mf-permanence-with-corona-conjugator
requires: []
artifacts:
  - research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md
---

Direct proof; literature inputs: Shulman arXiv:2603.13564v2 Theorem 16
(v2 BODY numbering; the intro's "Th. 20" is stale v1 numbering — statement
verified verbatim from the PDF 2026-08-26), Britton's lemma, and the
classical subgroup inclusion of group von Neumann algebras.  The corner
realization of the universal C-star HNN extension inside a full amalgam is
re-proved self-containedly (the idea is Ueda's, Illinois J. Math. 52
(2008)).

Write `D = C*(iota rho(G))`, `B_0, B_1` the two edge subalgebras, and
`Theta = Ad(W)|_{B_0}`.  (1) The universal C-star HNN `U = <D, u | u b u* =
Theta(b)>` embeds into `P = M_2(D) *_{B_0 + B_1} M_2(B_0)` by
`d |-> diag(d,0)`, `u |-> e_12 f_21`, with an explicit inverse on the image
built from `Ad(diag(1,u))`; pure universal-property computation.  (2) `P`
is MF by Shulman's criterion: `M_2(iota)` and `Ad(diag(1,W)) o M_2(iota)`
are embeddings of the two factors into a matrix corona agreeing on
`B_0 + B_1`, precisely because `W` conjugates the edges.  (3) The GNS
representation of the regular trace sends `D` onto a subalgebra of `L(G)`
carrying `iota rho(g)` to `lambda_G(g)`; composing with `L(G) <= L(R)` and
pairing with the unitary `lambda_R(t)` gives, by the universal property, a
representation `sigma : U -> B(l^2 R)` with `sigma(iota rho(g)) =
lambda_R(g)` and `sigma(u) = lambda_R(t)`.  The canonical homomorphism
`R -> U(U)` composed with `sigma` is the injective `lambda_R`, so `R`
embeds in the unitary group of the separable MF algebra `C*(image) <= U`,
and the trace of `L(R)` pulls back to the regular character.  Full
calculation: artifact Section 3.2.
