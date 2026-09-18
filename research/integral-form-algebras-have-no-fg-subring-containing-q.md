---
rg: 2
id: integral-form-algebras-have-no-fg-subring-containing-q
kind: claim
title: No finitely generated subring of M_n(A ⊗ K) contains a copy of Q when A has free abelian additive group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the group target, whose obstruction O1 (no residually finite overgroup) is group-theoretic; this is a ring-theoretic obstruction for subrings of scalar extensions of free abelian rings.
  q-embeds-in-a-corner-of-a-fp-toeplitz-ring: that exhibits a finitely presented ring containing Q; its generator A = (N+1)^(-1) is exactly what this obstruction says must lie outside every integral form.
---

**ESTABLISHED** through `integral-form-algebras-have-no-fg-subring-containing-q-proof`
(lane proof, not independently reviewed).

**Statement.** Let `A` be a ring, unital or not, whose additive group is free abelian.
Let `K` be any field and `n >= 1`. Then no finitely generated subring of
`M_n(A ⊗_Z K)` contains a subring isomorphic to `Q`, unital or not.

**Covered algebras.** Each of the following is `A ⊗ K` for a ring `A` with free abelian
additive group, and so has no finitely generated subring containing `Q`. The same holds
for all their matrix rings and corners.
- group algebras `K[G]`, with `A = Z[G]`;
- Leavitt algebras `L_K(1,n)`, Leavitt path algebras `L_K(E)`, Cohn and Toeplitz
  algebras, with `A` the corresponding algebra over `Z`, whose normal-form monomials
  are a `Z`-basis;
- Weyl algebras `A_m(K)`, with basis `x^i ∂^j`;
- Steinberg algebras `A_K(G)` of ample groupoids, where `A_Z(G)` is free abelian;
- Leavitt--Nekrashevych completions and crossed products whose defining data are
  integral (`leavitt-nekrashevych-completion-embeds-and-is-fp`), applied to `B ⊗ K`
  with `B` free abelian.

**Consequence for the GL_n(Q) swarm.** Every finitely generated ring that contains
`Q` needs a generator that no integral form carries, for example a resolvent such
as `(N+1)^(-1)` (`q-embeds-in-a-corner-of-a-fp-toeplitz-ring`). So no route to
`gl-n-q-embeds-in-fp-simple-group` can find `Q`, or `M_n(Q)`, inside a finitely
generated subring of a combinatorial Leavitt, group or Steinberg algebra, over any field.
