---
rg: 2
id: thompson-f-confined-subgroups-fix-finite-sets
kind: claim
title: A subgroup of Thompson's group F is confined exactly when it lies between the germ stabilizer in F' and the stabilizer of a finite subset of [0,1] (Chaudkhari 2018, Theorem 3.1)
distinct_from:
  full-group-confined-subgroups-are-finite-set-stabilizers: that concerns topological full groups of minimal effective groupoids over a Cantor space; this is Thompson's F acting on [0,1].
  thompson-f-two-transitive-stabilizers-minimal-not-confined: that shows particular point stabilizers are not confined; this characterizes all confined subgroups.
---

**ESTABLISHED** (literature import).

**Source.** M. Chaudkhari, *Confined subgroups of Thompson's group F and its embeddings into wobbling
groups*, arXiv:1809.05146v2 (4 Oct 2018), 10 pages.

**Verbatim definitions** (§2.3, §3).
- "Suppose that H and K are subgroups of G, then H is said to be confined by K if the closure of K-orbit
  of H does not contain the trivial subgroup."
- "the last condition is equivalent to the existence of a finite set P = {g1, g2, ..., gr} ⊆ G \ 1, such
  that ∀k ∈ K : kHk⁻¹ ∩ P ≠ ∅, we call such sets P confining. In case when K = G group H is simply
  called confined."
- "If a group G acts by homeomorphisms on a tolopological space X and Y ⊂ X, we call a rigid stabilizer
  of Y a subgroup of G consisting of all elements which fix the complement of Y pointwise. We denote this
  subgroup RG(Y), and stabilizer of Y is denoted StG(Y). Finally, a subgroup of all elements g ∈ G which
  act trivially on some neighborhood of Y is denoted St0G(Y) and is called the germ stabilizier of S."

**Verbatim theorem** (§3). "**Theorem 3.1.** A subgroup H of Thompson's group F is confined by the
commutator subgroup F′ of F if and only if there exists a finite subset of unit segment S ⊂ [0, 1] such
that St0F′(S) ≤ H ≤ StF(S). In particular, a subgroup is confined if and only if it is confined by F′."

**Also verbatim.**
- Remark 1: "Theorem 3.1 implies that graph Γ(F, H), with H being a confined subgroup of F, must be
  amenable."
- Theorem 4.1: "Assume that F acts on a set X and let p be any point in X. Then either orbital graph of
  p has exponential uniform growth or it is fixed by commutator subgroup of F."

**Reading notes.**
- `St_F(S)` is the setwise stabilizer. For finite `S` it is the pointwise stabilizer, since `F` preserves
  order.
- The "if" direction is proved in the source with `r = |S| + 1` elements of pairwise disjoint supports.
- The "only if" direction uses Matte Bon's theorem, quoted there as Theorem 3.2 ("Let G be a countable
  group acting by homeomorphisms of a Hausdorff space X, and assume that A ≤ G is a subgroup whose action
  on X is minimal and proximal. Let H ∈ Sub(G) be confined by A. Then there exists a non-empty open
  subset U ⊂ X and a finite index subgroup Γ of rigid stabilizer RA(U) such that H contains the derived
  subgroup [Γ, Γ]."). It then shows that the maximal open set `V` on which `H` contains all supported
  elements has finite complement.

DERIVATION
thompson-f-confined-subgroups-fix-finite-sets-citation
