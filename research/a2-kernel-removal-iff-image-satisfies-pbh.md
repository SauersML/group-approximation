---
rg: 2
id: a2-kernel-removal-iff-image-satisfies-pbh
kind: claim
title: The kernel of a type [A_2] action can be removed exactly when the action image embeds in a group with a type (A_2) action
distinct_from:
  a2-pairs-embed-in-a2-pairs-with-fng-kernels: that is the universal assertion, the first part of FFWZ Question 5.9; this proves that for each single action it is equivalent to the permutational Boone--Higman conclusion for the action image.
  a2-kernel-removal-forces-recursive-kernel: that gives a necessary computability condition for removal; this gives a necessary and sufficient condition.
  normalizer-extension-of-type-a-actor-is-a2-cover: that removes the kernel of one family of covers by a normalizer embedding; this removes the kernel of every action whose image has a faithful type (A_2) overgroup, by a direct product.
---

**ESTABLISHED** by `a2-kernel-removal-iff-image-pbh-proof`.

**Conventions.** Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, checked
against the PDF text extracted on MSI.
- **Type [A_2]** (Definition 1.3, n = 2). An action `G ↷ S` is of type [A_2] when:
  - `G` is finitely presented;
  - every point stabilizer is finitely generated;
  - there are finitely many orbits on `S x S`.

  It is of **type (A_2)** when it is moreover faithful. FFWZ note that this "was
  mostly called type (A) in [Zar24] and in subsequent work"; it is the "type (A)"
  of `permutational-boone-higman-conjecture`.
- **Embedding of pairs** (Definition 1.6). `(G,N)` embeds in `(G′,N′)` when some
  injective `ι: G → G′` has `ι(G) ∩ N′ = ι(N)`. Question 5.9 writes "sharply
  embeds" for this.
- **Removable.** Call an action `G ↷ S` of type [A_2] with kernel `K`
  *removable* when `(G,K)` embeds in `(G′,K′)` for some type [A_2] action
  `G′ ↷ S′` whose kernel `K′` is the normal closure of finitely many elements of
  `G′`. The first part of Question 5.9 asks whether every such action is
  removable:

  > "For G ↷ S an action of type [A_2] with kernel K, does there always exist an
  > action G′ ↷ S′ of type [A_2] with kernel K′ finitely normally generated, such
  > that (G,K) sharply embeds in (G′,K′)?"

**Theorem.** Let `G ↷ S` be of type [A_2] with kernel `K`. The following are
equivalent:
1. the action is removable;
2. `G/K` embeds in a group admitting a type (A_2) action.

In (2) ⇒ (1), the witness is `G′ = G x Λ` acting through its second factor.

**Corollaries.**
- **(a) Finitely presented images.** If `G/K` is finitely presented, then `K` is
  already finitely normally generated in `G`, and the action is removable with
  `(G′,K′) = (G,K)`.
- **(b) The universal question.** The first part of FFWZ Question 5.9
  (`a2-pairs-embed-in-a2-pairs-with-fng-kernels`) holds exactly when the image
  `G/ker(G ↷ S)` of every type [A_2] action embeds in a group admitting a type
  (A_2) action.

So the first part of Question 5.9 is the permutational Boone--Higman conclusion
for one class of finitely generated groups: the action images of type [A_2]
actions. That class contains every group with a type (A_2) action, and every
image acts faithfully on its set with finitely generated point stabilizers and
finitely many orbits of pairs, but need not be finitely presented
(`a2-action-with-non-finitely-presented-image`).

## Consequences (conditional, not part of the statement above)

1. **Modulo PBH it is a computability question.** Every group with a type
   (A_2) action has solvable word problem, so removal forces a recursive kernel.
   That is also `a2-kernel-removal-forces-recursive-kernel`. Conversely, if
   every type [A_2] kernel is recursive (`a2-action-kernels-are-recursive`),
   every action image is a finitely generated group with solvable word problem.
   `permutational-boone-higman-conjecture` then embeds it in a type (A_2) actor,
   and the Theorem makes the action removable. That is the route
   `a2-kernel-removal-via-pbh-and-recursive-kernels`.
2. **Theorem C actors carry the rest, modulo Boone--Higman for images.** Suppose
   every action image satisfies Boone--Higman, and the FFWZ Theorem C actor of
   every infinite finitely presented simple group is removable. Given an
   action image `Λ`, embed it in an infinite finitely presented simple group
   `Γ` (if the envelope is finite, use Thompson's `V`, which contains every
   finite group). The proof of FFWZ Theorem 5.1 makes `Γ`, hence `Λ`, act
   freely in the Theorem C actor `A ↷ X` of `Γ`, with kernel `K_A`. So `Λ`
   embeds in `A/K_A`, which has a type (A_2) action by the Theorem, and the
   original action is removable. Conversely, removability of every action gives
   both hypotheses, through Zaremsky's Corollary B
   (`type-a-action-gives-boone-higman-for-subgroups`).
3. **No effect on the second part of Question 5.9.** The product trick does not
   preserve relative simplicity. In `G x Σ`, the normal subgroup `N x Σ` is
   proper and not contained in `G x {1}` once `N ≠ G`. The relatively simple
   part belongs to `fp-relatively-simple-pairs-embed-with-fng-kernels`.

**Novelty.** FFWZ §5 asks the question and notes only that a positive first
part gives (relPBH) ⇒ (PBH). The equivalence above is not stated there. No later
literature search beyond the FFWZ text was made.
