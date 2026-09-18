---
rg: 2
id: gl-n-q-embeddings-are-branches-of-homomorphism-trees
kind: claim
title: Embeddings of SL_m(Q) into a group S are the infinite branches of a tree of homomorphisms of S-integer groups; finitely many classes per level suffice (Konig), and no finite level can refute a host containing all finite groups
distinct_from:
  gl-n-q-embeddings-detected-by-nontrivial-homomorphisms: that reduces an embedding of SL_m(Q) to one nontrivial element; this organizes the homomorphisms of the chain E_m(Z[1/k!]) into a tree and reads the root and its negation off the tree.
  gl-n-q-embeds-in-fp-simple-group: that is the embedding target; this is a reformulation of it and of its negation, with a sufficient finiteness condition.
  elementary-groups-over-polynomial-s-integers-are-fp: that gives finite presentation of E_n(Z[1/m][t_1..t_k]); this uses the case k = 0 to make each level of the tree finitely checkable.
---

**ESTABLISHED** by `gl-n-q-embeddings-are-branches-of-homomorphism-trees-proof`
(elementary; not independently reviewed; no novelty claimed). The general
"iff" for ascending unions is also being landed by lane gq-bhm-pattern as
`ascending-unions-embed-along-coherent-chains`; the new content here is (2)–(4).

## Statement

Fix odd `m >= 5`, write `H_k = E_m(Z[1/k!])`, so `SL_m(Q) = ⋃_k H_k` is an
ascending union, and let `S` be any group.

1. **Tree.** Let `T_S` be the rooted tree whose level-`k` vertices are the
   homomorphisms `ψ: H_k -> S` with `ψ(e_12(1)) != 1`, the parent of `ψ` being
   its restriction to `H_(k-1)`. Then `SL_m(Q)` embeds in `S` iff `T_S` has an
   infinite branch. If `S` is finitely presented with solvable word problem,
   `T_S` is a computable tree: each `H_k` is finitely presented (`m >= 4`), so
   a vertex is a finite tuple of words checked against finitely many relators.
2. **Konig recipe.** Let `A <= Aut(S)`. If for every `k` the set of
   `A`-classes (under post-composition) of embeddings `H_k -> S` is finite
   and nonempty, then `SL_m(Q)` embeds in `S`. The same holds for any
   ascending union `H = ⋃ H_k` in place of `SL_m(Q)`, for example
   `GL_n(Q) = ⋃ GL_n(Z[1/k!])`. It is enough to have nonempty finite sets
   `C_k` of classes with `C_(k+1)` restricting into `C_k`.
3. **Finite levels never refute hosts that contain all finite groups.** If `S`
   contains a copy of every finite group, for example Thompson's `V` or any
   group containing it, then every level of `T_S` is nonempty. For `S = V`,
   `T_V` still has no infinite branch, since `(Q,+) ⊄ V` (root, O3). So `T_V`
   is an infinite tree with every level nonempty and no branch: an explicit
   failure of Konig's lemma for infinitely branching trees.
4. **Biography of the negation.** Using
   `gl-n-q-embeddings-detected-by-nontrivial-homomorphisms` and
   `gl-n-q-targets-are-cofinal-in-n`, the root fails iff there is `m_0` such
   that for every odd `m >= m_0` and every one of the countably many finitely
   presented simple groups `S`, the computable tree `T_S` has no infinite
   branch.
   - This is a `Π^1_1` statement about a computable family of trees, and the
     root is `Σ^1_1`.
   - Every finitely presented simple group that contains `V`, or all finite
     groups, has all levels nonempty, so its refutation must use an infinitary
     invariant. The known kills are infinitary: Higman's root finiteness in
     `V`, distortion (root O4), residual finiteness (O1).
   - Conversely, level `k` of `T_S` can be empty only if `S` contains no
     `SL_m(F_p)` with `p > k`.

## Attempts

None beyond the statement.
