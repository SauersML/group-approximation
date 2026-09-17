---
rg: 2
id: boone-higman-iff-isolated-hosts-and-local-boone-higman
kind: claim
title: Boone--Higman is equivalent to the conjunction of Cornulier--Guyot--Pitsch Question 4 and Local Boone--Higman
distinct_from:
  boone-higman-iff-simple-kazhdan-decidable-inputs: that restricts the inputs to simple Kazhdan groups without changing the embedding problem; this splits the embedding problem into an overgroup statement and a statement about the universal theory of finitely presented simple groups.
  boone-higman-iff-infinite-simple-inputs: that restricts the inputs to infinite simple groups; this changes the statement, not the inputs.
  every-decidable-group-embeds-in-an-isolated-group: that is CGP Question 4, one of the two halves and implied by Boone--Higman; this is the two-sided equivalence that adds Local Boone--Higman as the other half.
  isolated-embedding-is-one-existential-sentence: that is the lemma used here; this is the equivalence it yields.
---

**ESTABLISHED** through `boone-higman-iff-isolated-hosts-and-local-boone-higman-proof`.

**Statement.** The following are equivalent.
1. `boone-higman-conjecture`: every finitely generated group with solvable word
   problem embeds in a finitely presented simple group.
2. Both of the following hold:
   - `every-decidable-group-embeds-in-an-isolated-group` (CGP Question 4): every
     finitely generated group with solvable word problem embeds in an isolated
     group;
   - `local-boone-higman-conjecture`: every finite system of equations and
     inequations without constants that has a solution in a finitely generated
     group with solvable word problem has a solution in some finitely presented
     simple group.

**Per-input form.** Let `H` be isolated. Then `H` embeds in a finitely presented
simple group iff the one existential sentence `Σ_H` of
`isolated-embedding-is-one-existential-sentence` holds in some finitely
presented simple group. Equivalently, `H` satisfies every universal sentence
true in all finitely presented simple groups. For an isolated input, embedding
and local embedding are the same problem.

**Reading for the counterexample direction.** Suppose Boone--Higman fails at `G`.
Then one of two things happens.
- `G` has no isolated overgroup.
- `G ≤ H` with `H` isolated. Then `H` also fails Boone--Higman, and the finite
  object `(presentation of H, discriminating set F)` gives a universal sentence
  `¬Σ_H`. It holds in every finitely presented simple group and fails in the
  decidable group `H`.

So on the second branch the invariant that every finitely presented simple
overgroup forces is a single universal first-order sentence. Complexity, Dehn
function, torsion-problem and finiteness invariants are needed only on the first
branch (see `local-boone-higman-conjecture`, Attempt 2).
