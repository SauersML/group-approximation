---
rg: 2
id: cocompact-fg-stabilizer-actions-force-finite-generation
kind: claim
title: A group acting on a connected graph with finitely many orbits of vertices and edges and finitely generated vertex stabilizers is finitely generated, so the adelic action of SL_2(Q) is not cocompact
distinct_from:
  sl-n-q-is-colimit-of-lattice-stabilizers: that presents SL_n(Q) as the colimit over the restricted product of chambers; this counts the orbits of that action and shows no cocompact model with finitely generated stabilizers exists for any of the gq targets.
  adelic-median-graph-automorphisms-are-restricted-products: that computes the full automorphism group of the adelic median graph; this is the orbit structure of SL_2(Q) and PGL_2(Q) on it, and a general finite-generation lemma.
---

**ESTABLISHED** through
`cocompact-fg-stabilizer-actions-force-finite-generation-proof`
(elementary and standard; no novelty is claimed; not independently reviewed).

## Statement

1. **Lemma.** Let a group `G` act on a connected graph `X` with finitely many
   orbits of vertices and finitely many orbits of edges. If every vertex
   stabilizer is finitely generated, then `G` is finitely generated.
2. **No cocompact models.** None of the groups
   - `(Q,+)`, `Aff(Q)`, `B_2(Q)`, `U_3(Q)`, and
   - `GL_n(Q)`, `SL_n(Q)`, `PGL_n(Q)`, `PSL_n(Q)` for `n >= 2`

   is finitely generated. So none of them acts on a connected graph, or on
   the 1-skeleton of a connected cell complex, with finitely many orbits of
   vertices and edges and finitely generated vertex stabilizers. In every
   cocompact action of one of these groups, some vertex stabilizer is not
   finitely generated. A permanence theorem whose inputs are cocompact
   actions with finitely presented vertex groups, such as Bux--Llosa
   Isenrich--Wu's for locally finite trees, can therefore never take one of
   these groups as input.
3. **The adelic action.** Let `X = ∏'_p T_p` be the restricted product of the
   Bruhat--Tits trees `T_p` of `(Q, v_p)` over all primes, relative to the
   base vertices `o_p = [Z_(p)^2]`. This is the median graph of
   `sl-n-q-is-colimit-of-lattice-stabilizers` for `n = 2`. Every vertex has
   infinite valence, so `X` is not locally finite.
   - **SL_2(Q)** acts with vertex stabilizers `SL(L) ≅ SL_2(Z)`, one for each
     Z-lattice `L ⊆ Q^2`. It has **infinitely many vertex orbits**: they
     correspond bijectively to the squarefree positive integers `c`, with
     representative `[Z ⊕ cZ]`. It has infinitely many edge orbits as well.
     So the action is not cocompact. This corrects item 1 of
     `research/artifacts/gq-gq-critic-2.md`, which calls it "one vertex orbit,
     i.e. cocompact". The quotient is the whole restricted product of
     chambers `∏'_p Δ_p`, an infinite-dimensional cube with one vertex for
     each finite set of primes.
   - **PGL_2(Q)** acts transitively on the vertices, with stabilizer
     `PGL_2(Z) = GL_2(Z)/{±I}`, which is finitely presented. It has **exactly
     one edge orbit for each prime `p`**, namely the edges in direction `p`.
     So it too has infinitely many edge orbits, as item 1 forces.

## Consequence for complexes of groups over the adelic building

Every complex of groups whose fundamental group is one of the groups in item
2, and whose local groups are finitely generated, has infinitely many cells
in its quotient. For the adelic building the quotient contains a loop, or an
edge, for every prime.

A permanence theorem that yields one of these groups must therefore handle
infinitely many orbits of cells. It must be uniform over the primes, not
merely local. Restricted to finite subcomplexes (finite sets `S` of primes),
the fundamental groups are the S-arithmetic groups `SL_2(Z[1/S])` (route of
`sl-n-q-is-colimit-of-lattice-stabilizers`, Step 5). Each of these lies in
`B_A` by `fp-self-similar-subgroups-satisfy-permutational-boone-higman`.
So the permanence question for this complex of groups is exactly the question
of embedding the chain `SL_2(Z[1/S])` coherently: the MT-C form of
`research/artifacts/gq-gq-critic-2.md`, section 3.
