---
rg: 2
id: group-approximable-tracial-algebras-closed-under-corners
kind: claim
title: Tracial algebras embeddable in ultraproducts of group factors are closed under corners, and local universality of a group factor is one membership question
distinct_from:
  group-factor-local-universality-reduces-to-ultraproducts: that shows a locally universal group factor exists iff every separable tracial von Neumann algebra embeds in an ultraproduct of group factors; this proves the class of such algebras is closed under corners and reduces that class statement to the membership of one locally universal algebra.
  thom-central-corner-criterion: that identifies hyperlinearity of a group with Connes embeddability of its twisted central corners; this puts every twisted central corner, of any group, into the class of algebras approximable by group factors, with no hyperlinearity hypothesis.
  some-countable-group-factor-is-locally-universal: that is the open existence question; this is a structural statement about the class it quantifies over.
---

**Definition.**  Write `GF` for the class of separable tracial von Neumann
algebras `(N, tau)` that admit a unital trace-preserving embedding into some
tracial ultraproduct `prod_V L(Gamma_n)` of group von Neumann algebras of
countable groups (with their canonical traces), for some ultrafilter `V`.

**Statement.**
1. Every Connes-embeddable separable tracial von Neumann algebra lies in `GF`.
   `GF` equals the Connes-embeddable class iff every countable group is
   hyperlinear.
2. `GF` is closed under unital trace-preserving subalgebras and under
   **corners**: if `N` is in `GF` and `p in N` is a nonzero projection, then
   `(pNp, tau(p)^(-1) tau)` is in `GF`.
3. In particular, for every countable group `Gamma`, finite central subgroup
   `J` and character `omega` of `J`, the corner `p_omega L(Gamma)` cut by the
   central projection `p_omega = |J|^(-1) sum_(j in J) conj(omega(j)) lambda(j)`,
   with normalized trace, lies in `GF`.  These are the twisted group von
   Neumann algebras of `Gamma/J` appearing in `thom-central-corner-criterion`.
4. The following are equivalent:
   - (a) some countable group `U` has `L(U)` locally universal;
   - (b) some separable locally universal tracial von Neumann algebra lies in `GF`;
   - (c) `GF` contains every separable tracial von Neumann algebra.

**What it changes.**  At the ultrapower level, compressions by projections, in
particular by central characters, cost nothing. Item 4 turns
`some-countable-group-factor-is-locally-universal` into a single membership
question, and item 1 shows that any non-Connes-embeddable member of `GF`
already gives a non-hyperlinear group.

**Proof.**  Route `group-approximable-tracial-algebras-corner-closure-proof`.
Elementary: projection lifting in ultraproducts, rational trace adjustment in
II_1 factors, and the amplification `qLq ⊗ M_k ≅ L ⊗ M_a` for `tau(q) = a/k`.
No novelty is claimed.
