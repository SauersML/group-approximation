---
rg: 2
id: stw59-nonabelian-unitary-component-groups
kind: claim
title: Simple unital AH algebras can have nonabelian unitary component groups, with central commutators of every order n>=2
root: true
distinct_from:
  stw59-exact-finite-abelian-unitary-component-groups: That realizes finite abelian groups with K1 zero; this realizes nonabelian central extensions of a nonzero K1 group, with a commutator of prescribed order.
  stw59-exact-factorial-unitary-component-groups: That computes a cyclic component group over an even-cell tower; this uses an odd-cell tower whose component group surjects onto K1 and is not abelian.
  stw59-simple-ah-non-k1-injective: That detects one non-null unitary killed by stabilization; here the kernel of the K1 map is computed as Z/n! and a commutator witnesses it.
artifacts:
  - research/artifacts/stw59-nonabelian-unitary-component-groups-2026-09-11.md
---

For every n>=2 there are a separable simple unital nuclear stably finite
infinite-dimensional AH algebra B_n, with a unique trace and stable rank
exactly two, and unitaries u, v in B_n, such that:

- the canonical map U(B_n)/U0(B_n) -> K1(B_n) is surjective with central
  kernel Z/n!;
- the commutator u v u* v* has order exactly n in U(B_n)/U0(B_n);
- K1(B_n) is free abelian of countably infinite rank.

So U(B_n)/U0(B_n) is not abelian. The products uv and vu lie in different
components of U(B_n), while diag(uv,1) and diag(vu,1) lie in one
component of U(M2(B_n)).

This is the simple analogue of Blackadar's classical nonsimple example
(K-Theory for Operator Algebras, 8.1.2(d), from Araki--James--Thomas):
C(U(2) x U(2), M_2), whose coordinate unitaries do not commute up to
homotopy. In the simple classes known to be K1-injective (purely
infinite, stable rank one, real rank zero, Z-stable), the component group
embeds in K1 and is abelian.

The theorem refutes STW Problem LIX a second time, with a commutator as
witness. No other named problem is claimed. Complete proof, written by
the lix-sweep lane; not yet independently reviewed.

The construction is the twisted factorial tower with base
S^1 x S^(2n-1) x products of CP^(n 2^j) and dense-tail evaluation maps.

ROUTES

stw59-nonabelian-component-groups-limit-proof
