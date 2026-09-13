---
rg: 2
id: torsor-cfi-port-profiles-are-cosets
kind: claim
title: Torsor CFI gadgets over any finite group have coset port profiles at the q, qa and qc levels, so nonabelian torsor symmetry does not cross the affine barrier atom by atom
artifacts:
  - research/artifacts/ex-kac-quantum-compiler-torsor-cfi-2026-09-13.md
  - research/artifacts/ex-kac-quantum-compiler-torsor-profiles-2026-09-13.md
distinct_from:
  central-character-profiles-affine-under-odd-tensor-products: that closes ordinary-group gadgets by tensoring three representations; this closes torsor CFI isomorphism gadgets over any finite group, where the ternary operation is composition of quantum isomorphisms plus a twist identity.
  torsor-cfi-isomorphism-algebra-is-coset-constraint-algebra: that computes the isomorphism algebra of one torsor CFI pair; this proves that the set of scalar port values realizing an isomorphism is a coset of a subgroup.
  closure-safe-support-is-exactly-the-colored-iso-rung: that gives the support boundary for one colored isomorphism gap; this is an expressivity no-go for a gadget technology in isomorphism syntax.
---

**ESTABLISHED** by `torsor-cfi-port-profiles-are-cosets-proof`.  It has not
been reviewed by an ex-verify lane.

**Setting.**
- Torsor CFI data `(H,[n],S)` with non-port relations `R_k`, `R'_k`, as in
  `torsor-cfi-isomorphism-algebra-is-coset-constraint-algebra`.
- Port variables `P`.  For `π in H^P`, `G_H(R, π)` adjoins, for each
  `i in P`, a one-variable context with relation `{π_i}`.
- `X = G_H(R, π^0)` and `Y_σ = G_H(R', σ)`.

**Theorem.**  Let `t in {q, qa, qc}`.
- `N''_t = {δ : G_H(R',e) ≅_t G_H(R',δ)}` is a subgroup of `H^P`.
- `N_t = {σ : X ≅_t Y_σ}` is empty or a right coset `N''_t σ_0`.

So `N_t` is closed under `(σ,τ,ρ) |-> σ τ^(-1) ρ`.

**Boolean ports.**  Read each port bit through an involution `t_i in H`.  The
realizable bit patterns then form an affine subspace of `F_2^P`.  A torsor CFI
gadget complete at level `t` on the sectors `(+,+)`, `(-,+)` and `(+,-)` of
two ports is complete at level `t` on `(-,-)`.

**Mechanism.**  `≅_t` is an equivalence relation on colored digraphs.
Compose magic unitaries in `A (x) B`, transpose over `A^op`, and use closure of
each level under tensor products.  By the dictionary theorem,
`A(Iso(Y_σ,Y_τ))` has the same presentation as
`A(Iso(G_H(R',e), G_H(R',τσ^(-1))))`.

**Consequence for compilers.**  Suppose a compiler realizes each verifier
predicate by a torsor CFI gadget, over any finite group, including nonabelian
ones, with scalar port sectors and atom-by-atom completeness.  Then it can
only realize coset relations, and affine relations on Boolean ports.  So such
a compiler meets the affine firewall of
`jnvwy-active-output-has-no-affine-safe-perfect-model`.

**What survives.**
1. Gadget families in isomorphism syntax whose port variations are not twists
   of one graph.  The groupoid remains, but the twist identity, the only
   torsor input, does not.
2. Non-scalar port sectors.
3. A single torsor CFI pair with a gap.  That is exactly a coset-safe
   `H`-valued constraint system with a perfect trace and no `R^U` model.
