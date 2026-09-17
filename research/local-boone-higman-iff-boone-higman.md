---
rg: 2
id: local-boone-higman-iff-boone-higman
kind: claim
title: Local Boone--Higman is equivalent to Boone--Higman, already for single-inequation systems over finitely presented decidable groups
distinct_from:
  boone-higman-iff-isolated-hosts-and-local-boone-higman: that splits Boone--Higman as CGP Question 4 AND Local Boone--Higman; this shows the second conjunct alone is equivalent to Boone--Higman, so the first conjunct is a redundant premise and the split is degenerate.
  isolated-embedding-is-one-existential-sentence: that turns embedding of an ISOLATED group into one existential sentence using a discriminating set; this needs no isolated overgroup and no discriminating set, only one nontrivial element of a simple subgroup of a finitely presented decidable envelope.
  bht-trivial-normal-intersection-envelope: that produces a finitely presented envelope whose proper normal subgroups miss the input; this uses the Thompson and Clapham envelopes to show that homomorphisms into hosts, not normal subgroups of the envelope, detect embeddability, and it needs the envelope to be decidable, which that node does not supply.
  boone-higman-iff-infinite-simple-inputs: that restricts the inputs of Boone--Higman to simple groups; this changes the statement from embeddings to finite systems and shows the change costs nothing.
  local-boone-higman-conjecture: that is the open local statement; this is the theorem that it is equivalent to the flagship.
---

**ESTABLISHED** through `local-boone-higman-iff-boone-higman-proof`.

**Theorem (host-class principle).** Let `𝒦` be any class of groups. The
following are equivalent.

- **(a) Global.** Every finitely generated group with solvable word problem
  embeds in some member of `𝒦`.
- **(b) Local.** Every finite system `u_1(y) = 1, ..., u_d(y) = 1,
  v_1(y) ≠ 1, ..., v_k(y) ≠ 1` without constants that has a solution in a
  finitely generated group with solvable word problem has a solution in some
  member of `𝒦`.
- **(c) Quasi-identities over finitely presented decidable groups.** For every
  finitely presented group `H` with solvable word problem and every `g ≠ 1` in
  `H`, there are `K ∈ 𝒦` and a homomorphism `φ : H → K` with `φ(g) ≠ 1`.
  Equivalently: every quasi-identity `∀y (r_1(y) = 1 ∧ ... ∧ r_d(y) = 1 → w(y) = 1)`
  that holds in every member of `𝒦` holds in every finitely presented group
  with solvable word problem.

Nothing about `𝒦` is used: no closure property, no simplicity of its members.

**Specialization.** With `𝒦 = fps`, the finitely presented simple groups, (a) is
`boone-higman-conjecture` and (b) is `local-boone-higman-conjecture`. So

`boone-higman-conjecture ⟺ local-boone-higman-conjecture ⟺` (c) for `fps`.

In (c) the system has **one** inequation, and its equations are a finite
presentation of a decidable group. This is formally the weakest of the three.

## Consequences

1. **Attempt 3 of `local-boone-higman-conjecture` is answered.** Local
   Boone--Higman implies `every-decidable-group-embeds-in-an-isolated-group`
   (via Boone--Higman and `fp-simple-groups-are-isolated`). The premise CGP
   Question 4 in `boone-higman-via-isolated-overgroup-and-local-boone-higman` is
   redundant, and the claim there that the two halves "can fail separately as
   far as is known" is false in one direction: if Question 4 fails, Local
   Boone--Higman fails.
2. **Obstruction to the class of local approaches.** Any method that proves
   Local Boone--Higman by realizing each finite piece in a different host
   (compactness, limits in the space of marked groups, ultraproducts of
   finitely presented simple groups, residual properties) proves Boone--Higman
   itself. The invariant is the Thompson simple envelope `S` inside the
   Clapham envelope `H`: one finite piece, the relators of `H` plus `g ≠ 1`
   for a single `g ∈ S`, already forces an injective homomorphism on all of
   `S`. The local method dies exactly at "a different host per piece is
   easier": the step where it would gain freedom is the step where simplicity
   of `S` removes it.
3. **Unconditional counterexample certificate.** If Boone--Higman fails at `G`,
   then there is a single quasi-identity `∀y (r(y) = 1 → w(y) = 1)` that holds
   in every finitely presented simple group and fails in a finitely presented
   group `H` with solvable word problem. Here `r` presents the Clapham
   envelope of a Thompson simple envelope of `G × Z`, and `w` is any nontrivial
   element of that simple envelope. The per-input reading of
   `boone-higman-iff-isolated-hosts-and-local-boone-higman` gave such a
   universal sentence only on the branch where `G` has an isolated overgroup;
   this gives it on every branch, with one inequation.
4. **Ultraproduct form.** By Łoś's theorem, (b) for `fps` is equivalent to:
   every finitely generated decidable group embeds in an ultraproduct of
   finitely presented simple groups. So Boone--Higman is equivalent to that
   statement.
5. **Other host classes.** The same equivalence holds for any variant whose
   input class is "finitely generated with solvable word problem", for example
   with `𝒦` the finitely presented simple Kazhdan groups, or the finitely
   presented simple groups acting with a given property. Only (a), (b) and (c)
   for the same `𝒦` are compared.
