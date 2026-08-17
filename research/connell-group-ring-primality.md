---
rg: 2
id: connell-group-ring-primality
kind: claim
title: A group ring is prime exactly when the coefficient ring is prime and the group has no nontrivial finite normal subgroup
distinct_from:
  leavitt-unit-group-algebra-is-prime: that is the single instance this graph consumes, `F_2[R^x]` for the binary Leavitt unit group, and its content is the verification of the group-side hypothesis; this is the general criterion, imported from the literature and true for every group and every coefficient ring.
  stable-finiteness-reduces-to-prime-field: that is also an imported general group-ring fact, but about which coefficient fields a direct-finiteness search must cover; this is about primality of the ring, and the word prime means a different thing in each.
  leavitt-unit-group-has-no-finite-normal-subgroup: that verifies the group-side hypothesis for one specific group, from theorems formalized in this repository; this is the general criterion that consumes such a hypothesis, imported and proved nowhere here.
  finite-infranormal-subgroup-is-normal: that is an internal lemma about when a finite subgroup is normal, used in the approximation lanes; this is an imported criterion whose hypothesis is the absence of any nontrivial finite normal subgroup, and it neither needs nor supplies that lemma.
  mf-finite-normal-tracially-visible: that says finite normal subgroups of an MF group are seen by traces, an approximation-theoretic statement; this is a ring-theoretic criterion in which finite normal subgroups appear as the obstruction to primality, and the two share only the phrase.
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

For a ring `A` and a group `G`, the group ring `A[G]` is a prime ring if and
only if `A` is prime and `G` has no nontrivial finite normal subgroup.

This is Connell's Theorem 8.  The direction consumed here is the sufficient
one, and only over a field: if `G` has no nontrivial finite normal subgroup
then `K[G]` is prime.

## What is actually needed downstream

Less than the full criterion.  The Delta-method form suffices: if
`Delta(G) = 1` — no element of `G` has a conjugacy class of finite size other
than the identity — then `K[G]` is prime.  In the one application here
(`leavitt-unit-group-algebra-is-prime`) that hypothesis is available directly
and for a stronger reason than usual: the group has no proper subgroup of
finite index at all, so every finite conjugacy class is a singleton and
`Delta(G) = Z(G)`.

The full statement is imported anyway because it is the form the literature
states, and because the finite-normal-subgroup phrasing is what makes the
verification legible: `Delta^+(G) = 1` is exactly "no nontrivial finite normal
subgroup".
