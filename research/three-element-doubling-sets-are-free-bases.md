---
rg: 2
id: three-element-doubling-sets-are-free-bases
kind: claim
title: In any group, {1, a, b} doubles every finite set iff a, b freely generate a free group; so without free subgroups no set of at most three elements doubles, and a group with Tarski number 5 has a four-element doubling set
distinct_from:
  thompson-f-has-no-free-subgroups: that is the Brin--Squier theorem about F; this is a statement about every group, which turns the absence of free subgroups into a counting statement about sets of at most three elements.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that says F is non-amenable iff some set of monomials of one degree doubles; this characterizes three-element doubling sets in any group, and so excludes every set of at most three monomials.
  thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs: that is a sufficient condition for a set of monomials to double; this is a necessary and sufficient condition for three-element sets, in any group.
artifacts:
  - research/artifacts/three-element-doubling-sets-2026-09-16.md
---

Let `G` be a group. A finite set `S ⊆ G` **doubles** if `|S Y| >= 2|Y|` for every finite `Y ⊆ G`.
Doubling is invariant under `S -> g S h`, and subsets of non-doubling sets do not double.

1. **Three elements.** For `a, b ∈ G` with `1, a, b` pairwise distinct, `{1, a, b}` doubles iff `a`
   and `b` freely generate a free group of rank 2.
2. **No free subgroups.** If `G` has no non-abelian free subgroup, then every finite `S ⊆ G` with
   `|S| <= 3` has a finite nonempty `Y` with `|S Y| < 2|Y|`.
3. **Four is possible.** If the Tarski number of `G` is 5, then `G` has no non-abelian free
   subgroup and contains a doubling set with exactly four elements. Such groups exist (M. Ershov,
   G. Golan, M. Sapir, *The Tarski numbers of groups*, Adv. Math. 284 (2015) 21–53,
   arXiv:1401.2202, abstract; G. Golan, *Groups with Tarski number 5*, arXiv:1406.2097). So item 2
   is optimal among statements that use only the absence of free subgroups.

**Use for `F`.** Combined with `thompson-f-has-no-free-subgroups`, item 2 gives the Thompson-group
statements of `thompson-f-support-three-pairs-have-common-multiples`: no set of at most three
monomials doubles, and pairs in `K[F]` with joint support of size at most three have common
multiples. Item 3 says that a four-element version for `F` would need input specific to `F`.

**Scope.**
- Item 1, direction (1) ⇒ (2), is the ping-pong half of the Jónsson–Dekker theorem (Tarski number 4
  iff a non-abelian free subgroup), with a 2-fold matching for `{1, a, b}` in place of a four-piece
  paradoxical decomposition. The statement may well be folklore; novelty is not claimed, and it was
  not found in the sources consulted (artifact §6).
- The proof uses the infinite Hall theorem for countable, locally finite bipartite graphs, proved in
  the artifact from the finite Hall theorem and König's lemma.
- Item 3 imports only the existence of a group with Tarski number 5, from the two abstracts above
  (the constructions were not re-read). The implication "Tarski number 5 ⇒ no free subgroup and a
  four-element doubling set" is proved in the artifact (§4), using Definition 1.1 of
  arXiv:1401.2202v4.

Proof route: `three-element-doubling-sets-are-free-bases-proof`.
