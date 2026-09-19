---
rg: 2
id: elek-szabo-envelope-loses-torsion-free-kazhdan-control-proof
kind: route
title: Read cycle profiles and countable descent in the universal sofic group
target: elek-szabo-envelope-loses-torsion-free-kazhdan-control
requires:
  - simple-sofic-total-mf-radical
  - torsion-free-lef-kazhdan-non-rf-seed
---

Elek--Szabo, *Hyperlinearity, essentially free actions and L2-invariants. The
sofic property*, Math. Ann. 332 (2005), arXiv:math/0408400, Proposition 2.3,
Theorem 1 and Corollary 3.1, give the required facts.

Proposition 2.3(3) realizes every admissible cycle-density profile.  Set
`P_2=1/2` and every other `P_t=0`; the resulting nonidentity element has order
two.  Varying `P_2` and using conjugacy-profile invariance in Proposition
2.3(4) produces uncountably many elements.  A discrete property-`(T)` group
is finitely generated and therefore countable, so the ambient group cannot
have property `(T)`.  Theorem 1 gives simplicity, soficity and universality,
while Proposition 2.3(5) gives bounded normal generation for each fixed
nontrivial conjugacy class.  Since a property-`(T)` subgroup makes the pair
relatively property `(T)`, these facts prove `(ESK1)` and `(ESK2)`.

Corollary 3.1 only places a countable subgroup inside a countable simple
intermediate subgroup.  Its iterative conjugator construction has no clause
controlling element orders or a finite Kazhdan set.  If the union were
Kazhdan, it would be finitely generated and would have to stabilize inside a
finite stage; no such stabilization is provided.

Finally, the Kida--Thom seed is LEF and hence MF, so embedding it alone
provides no nonzero intrinsic MF-radical element.  The unconditional Lean
envelope instead embeds the Clifford witness.  The theorem
`manuscript_simpleSoficEnvelope_no_torsionFree_image` in
`SimpleSoficEnvelopeUnconditional.lean` proves that every homomorphism from
that envelope to a torsion-free group is trivial, because the injectively
embedded Clifford sign is a nontrivial involution and simplicity propagates
its kernel.  This proves the final obstruction.
