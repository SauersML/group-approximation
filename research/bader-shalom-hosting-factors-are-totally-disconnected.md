---
rg: 2
id: bader-shalom-hosting-factors-are-totally-disconnected
kind: claim
title: If a Bader-Shalom lattice in a product of two groups contains a finitely generated infinite simple group, both factors are totally disconnected, and each factor contains a cocompact lattice that embeds in a compact group and is commensurated by the dense projection of the lattice
distinct_from:
  one-haagerup-factor-kills-bader-shalom-universality: that kills one analytic factor class (Haagerup) against one Kazhdan probe; this kills every factor with nontrivial identity component against every finitely generated infinite simple subgroup, and turns the surviving totally disconnected case into lattice data in each factor.
  cat0-factors-kill-bader-shalom-universality: that kills finite-dimensional CAT(0) factors with compact stabilizers against the golden-mean probe; this uses no probe beyond simplicity and no geometry, and reaches non-linear factors that are not totally disconnected, which Attempt 1(a) of the target left open.
  bader-shalom-normal-subgroup-theorem: that gives just-infiniteness and injective projections; this consumes the injectivity to force total disconnectedness, and then to build residually compact uniform lattices in each factor.
  almost-connected-groups-omit-fg-infinite-simple-groups: that is the general exclusion for almost connected targets; this is its application to Bader-Shalom factors, together with the totally disconnected lattice data that follow from it.
---

**ESTABLISHED** through `bader-shalom-hosting-factors-are-totally-disconnected-proof`.

## Setting

Let `Γ < G_1 × G_2` satisfy the hypotheses of `bader-shalom-normal-subgroup-theorem`
with `n = 2`:
- each `G_i` is non-discrete, compactly generated, locally compact,
  just-non-compact, and has no nontrivial abelian normal subgroup;
- `Γ` is a cocompact lattice with dense projections `p_i(Γ)`.

Assume `Γ` contains a finitely generated infinite simple subgroup `S`. This
holds whenever `Γ` witnesses `decidable-simple-groups-embed-in-bader-shalom-lattices`.

## Statements

1. **Total disconnectedness.** Each `G_i` is totally disconnected: `G_i^0 = 1`.
2. **Lattice data in the other factor.** Let `U_1 ≤ G_1` be a compact open
   subgroup, which exists by van Dantzig. Put `O = U_1 × G_2`,
   `Λ = Γ ∩ O` and `Δ_2 = p_2(Λ)`. Then:
   - (a) `Δ_2` is a cocompact lattice in `G_2`, and `p_2 : Λ → Δ_2` is an
     isomorphism;
   - (b) `Δ_2` is isomorphic to a subgroup of the compact group `U_1`, through
     `p_1 ∘ (p_2|_Λ)^{-1}`;
   - (c) `p_2(Γ)` is a dense subgroup of `G_2` that commensurates `Δ_2`, and
     `[p_2(Γ) : Δ_2] = ∞`.

   The same holds with `1` and `2` exchanged.
3. **Position of the simple subgroup.** For each `i` and each compact open
   `U_i ≤ G_i`, put `S_i = S ∩ p_i^{-1}(U_i)`.
   - `S_i` is a commensurated subgroup of `S` of infinite index, and it is
     isomorphic to a subgroup of the compact group `U_i`.
   - Exactly one of the following holds:
     - (D) `p_i(S)` is discrete in `G_i`, which happens exactly when `S_i` is
       finite;
     - (N) `S_i` is an infinite, commensurated subgroup of infinite index that
       embeds in a compact group.
4. **Class kill.** For every factor pair `(G_1, G_2)` in which some factor has
   no cocompact lattice isomorphic to a subgroup of a compact group, no
   Bader–Shalom lattice in `G_1 × G_2` contains a finitely generated infinite
   simple group. This covers in particular any factor with no cocompact lattice
   at all.

## The invariant and where the hosts die

**Item 1.**
- *Invariant:* the identity component and the adjoint representation of a Lie
  quotient.
- *Step where it dies:* suppose `G_i^0 ≠ 1`. Just-non-compactness makes `G_i`
  almost connected. The injective projection `p_i|_S` (NST item 2) then
  contradicts `almost-connected-groups-omit-fg-infinite-simple-groups`.
- *What this kills:* every factor that is not totally disconnected. That
  includes, a priori, non-linear ones. Attempt 1(a) of the target killed only
  factors that are already linear, and Attempt 2 assumed total disconnectedness
  for the survivors informally. Item 1 proves it.

**Item 4.**
- *Invariant:* existence of a uniform lattice that embeds in a compact group.
- *Step where it dies:* the intersection `Γ ∩ (U_1 × G_2)` of item 2.

## Consequences for P1

Every lattice witnessing P1, for any input, has the following shape.
- Both factors are non-discrete, compactly generated, totally disconnected
  locally compact groups. So each acts vertex-transitively, with compact open
  stabilizers, on a connected locally finite Cayley–Abels graph `X_i`, and `Γ`
  acts on `X_1 × X_2` with stabilizers `Γ ∩ (U_1 × U_2)`. These are finite,
  being discrete and compact.
- `G_2` contains a cocompact lattice `Δ_2` that embeds in the profinite group
  `U_1`, with dense commensurator. So `G_2` lies in the closure of the
  commensurator of a residually compact uniform lattice. The symmetric statement
  holds for `G_1`.

With the probes of Attempt 2, the golden-mean probe `P` and the Kazhdan probe
`H`, each factor must satisfy the following.
- It is a non-Haagerup tdlc group.
- It contains a uniform lattice that embeds in a compact group, with dense
  commensurator.
- It satisfies (D) or (N) of item 3 for `H` and for `P`. In case (D), the
  infinite simple probe sits discretely in the factor.

**Trust.** The standard facts used without citation are:
- existence and properness of Cayley–Abels graphs, in the paragraph above only;
- the identity component is closed and normal;
- discrete subgroups of Hausdorff groups are closed.

Examples of factors with no lattice, such as the Neretin groups
(Bader–Caprace–Gelander–Mozes, *Simple groups without lattices*, Bull. LMS 44
(2012)), are named from memory, not quoted. They serve only as illustrations of
item 4, and item 4 does not depend on them.
