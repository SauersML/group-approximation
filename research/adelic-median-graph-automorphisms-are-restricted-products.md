---
rg: 2
id: adelic-median-graph-automorphisms-are-restricted-products
kind: claim
title: Every automorphism of the adelic median graph acts prime by prime, so no finitely generated group of its automorphisms contains the standard SL_2(Q), and any envelope must mix the primes
distinct_from:
  cocompact-fg-stabilizer-actions-force-finite-generation: that counts the orbits of SL_2(Q) and PGL_2(Q) on the adelic median graph; this computes the full automorphism group of the graph and rules out envelopes acting on it.
  no-q-in-tree-product-actions-with-finite-stabilizers: that excludes (Q,+) from actions on products of trees with finite vertex stabilizers; this allows arbitrary stabilizers but only automorphisms of the adelic graph, and rules out finitely generated groups of them.
  lifts-add-no-unipotent-divisibility: that rules out central and covering lifts as hosts; this rules out groups of automorphisms of the development of the adelic complex of groups.
artifacts:
  - research/artifacts/gq-referee-a-adelic-tree-product-lemmas.md
---

**ESTABLISHED** through
`adelic-median-graph-automorphisms-are-restricted-products-proof`
(elementary; no novelty is claimed; not independently reviewed).
*Reviewed (gq-referee-a, proof-gap lens, 2026-09-18):* PASS. See
`research/artifacts/gq-referee-a-adelic-tree-product-lemmas.md`.

## Setup

Let `X = ∏'_p T_p` be the restricted product of the Bruhat--Tits trees of
`(Q, v_p)` relative to the base vertices `o_p = [Z_(p)^2]`. Its vertices are the
families `x = (x_p)` with `x_p = o_p` for almost all `p`. Two vertices are
adjacent when they differ in exactly one coordinate `p`, where they are
adjacent in `T_p`. That coordinate is the *direction* of the edge. `T_p` is
`(p+1)`-regular. `X` is the development of the complex of groups of
`sl-n-q-is-colimit-of-lattice-stabilizers` for `n = 2`.

## Statement

1. **Automorphisms.** Every graph automorphism `φ` of `X` preserves directions
   and has the form `φ = (φ_p)_p` with `φ_p ∈ Aut(T_p)` and `φ_p(o_p) = o_p` for
   all but finitely many `p`. Conversely every such family is an automorphism.
   So `Aut(X)` is the restricted product `∏'_p (Aut(T_p) : Aut(T_p)_(o_p))`.
2. **Finitely generated subgroups.** Every finitely generated subgroup `E` of
   `Aut(X)` lies in `A_S × K_S` for some finite set `S` of primes, where
   `A_S = ∏_(p in S) Aut(T_p)` and `K_S = ∏_(q not in S) Aut(T_q)_(o_q)`. `K_S` is
   profinite.
3. **What `E` can hold.** The projection `E -> K_S` kills:
   - every divisible subgroup of `E`, in particular every copy of `(Q,+)`;
   - every subgroup of `E` isomorphic to `SL_2(Q)`, `PSL_2(Q)`, `GL_2(Q)` or
     `PGL_2(Q)`, restricted to its commutator subgroup, which is `SL_2(Q)` or
     `PSL_2(Q)`.

   So every such subgroup of `E` acts trivially on the factors `T_q` with
   `q` not in `S`. It acts only on the finite product `∏_(p in S) T_p` of
   locally finite trees.
4. **The standard action does not extend.** `SL_2(Q)` acts on `X` coordinatewise
   and moves `o_q` for every prime `q`. For instance `e_12(1/q)` does. So no
   finitely generated group of automorphisms of `X` contains the image of
   `SL_2(Q)`, or of `PSL_2(Q)` or `(Q,+)`, under the standard action. Indeed,
   for every finitely generated `E ≤ Aut(X)`, `E ∩ SL_2(Q) ⊆ SL_2(Z[1/S])` and
   `E ∩ PGL_2(Q) ⊆ PGL_2(Z[1/S])`.

## Consequence for permanence over the adelic building

A permanence theorem for the adelic complex of groups has to produce a
finitely presented, in particular finitely generated, group containing its
fundamental group `SL_2(Q)`. By item 4, that envelope cannot be a group of
automorphisms of the development `X` extending the given action. That rules
out the naive "almost everything acts on the building" design. By item 3, even
an abstract copy of `SL_2(Q)` inside a finitely generated group of
automorphisms of `X` sees only finitely many primes.

An envelope must therefore act on a space where the prime coordinates are
*not* separately preserved. Its generators must carry the structure at one
prime to another. `gl-n-q-lies-in-prime-shift-permutation-group` does this on
`Q^n`, where `σ` sends `p_k` to `p_(k+1)`. This is the MT-C coherence invariant
of `research/artifacts/gq-gq-critic-2.md` made concrete. The *prime support*
of a finite generating set is bounded for every finitely generated group of
automorphisms of `X`, and unbounded along the chain `SL_2(Z[1/S])`. It
obstructs a class of envelopes, not the embedding problem itself.

Item 1 uses that the valences `p+1` are pairwise distinct. On a restricted
product of isomorphic trees an automorphism could also permute the factors, and
the prime support would no longer be an invariant.
