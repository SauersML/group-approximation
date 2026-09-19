---
rg: 2
id: nv-orbit-relations-are-hyperfinite
kind: claim
title: Every subgroup of nV has hyperfinite measured orbit relation on the cube C^n, so no essentially free probability-preserving action of a non-amenable group sits inside nV
distinct_from:
  thompson-f-interval-orbit-relation-is-hyperfinite: that is the n = 1 interval relation of F; this is the coordinatewise tail relation of nV on C^n and its consequence for free probability-preserving models
  brin-thompson-2v-is-not-a-t-menable: that is the negation of the goal; this kills only the class of refutations that realize a Burger-type pair through a free probability-preserving model
---

**ESTABLISHED.** Let `n ≥ 1`, `C = {0,1}^N`, and let `nV` act on `C^n` by brick maps.

1. **(Hyperfinite.)** For every subgroup `G ≤ nV` and every `G`-quasi-invariant σ-finite
   Borel measure `μ` on `C^n`, the measured orbit relation `(R_G, μ)` is hyperfinite.
2. **(No free probability-preserving models.)** If `G ≤ nV` preserves a Borel probability
   measure `μ` on `C^n` and acts `μ`-essentially freely, then `G` is amenable. Equivalently,
   for a countable non-amenable `Γ` with an essentially free probability-preserving action on a
   standard space `(X, m)`, no Borel isomorphism `φ : X → C^n` (defined off a null set)
   conjugates the action into `nV`.
3. **(Burger models die.)** The following affine actions are essentially free and preserve Haar
   probability. By 2, none of them is Borel-conjugate into any `nV`:
   - `Z^2 ⋊ Λ` on `Z_p^2`, for every non-amenable `Λ ≤ SL_2(Z)`, every prime `p`, and more
     generally on any infinite profinite completion of `Z^2` to which `Λ` extends;
   - `R^2 ⋊ EL_2(R)` on `F_p[[t]]^2` for `R = F_p[t]`.

**Consequence for the goal.** Suppose one refutes `brin-thompson-groups-nv-are-a-t-menable`
through a Burger pair `(Λ ⋉ A, A)` embedded in `nV`, with `A = Z^2` or `A = F_p[t]^2`. Then the
embedding cannot be the natural completion model conjugated by some identification of the
Cantor set. Nor can it be any other model in which the non-amenable pair acts essentially
freely preserving a probability measure.

- *Invariant:* measured hyperfiniteness of the orbit relation on `C^n`.
- *Failing step:* amenability of the orbit relation of a free probability-preserving action.

This matches the earlier observation that shears such as `e_12(t)` or `(x,y) ↦ (x+y, y)` over
`Z_2` are carry-propagating cellular-automaton maps rather than brick maps. It now covers
every conjugate of those maps, not only the standard coordinates.

**Not killed.** Embeddings in which the pair acts with non-amenable stabilizers on a set of
positive measure. Embeddings with no invariant probability measure at all, which is the
generic case for subgroups of `nV`.

**Scope.** The proof imports the following as standard, without verbatim quotes, as in the
precedent `thompson-f-interval-orbit-relation-is-hyperfinite`:
- Zimmer 1977: non-singular actions of amenable groups have amenable orbit relations;
- Connes–Feldman–Weiss 1981: amenable relations are hyperfinite;
- Zimmer 1984, *Ergodic Theory and Semisimple Groups*, Prop. 4.3.3: an essentially free
  probability-preserving action with amenable orbit relation forces the acting group to be
  amenable.

Part 1 for `nV` is very likely folklore; no novelty is claimed for it.

Proof route: `nv-orbit-relations-are-hyperfinite-proof`.
