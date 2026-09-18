---
rg: 2
id: countable-simple-fp2-needs-all-three-hypotheses-proof
kind: route
title: "Three established uncountable witnesses, one per dropped hypothesis, plus contrapositives of the FP_2 and kernel criteria"
target: countable-simple-fp2-needs-all-three-hypotheses
requires:
  - simple-fp2-countability-iff-scattered-kernel-spaces
  - fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup
  - every-countable-group-embeds-in-an-fp2-group
  - constructed-continuum-of-finitely-generated-groups
  - kazhdan-hyperbolic-continuum-non-fng-maximal-kernels
  - v-times-shift-alternating-group-restrictions-are-simple
  - v-times-shift-restriction-kernels-are-perfect
---

**Reformulation.** By `simple-fp2-countability-iff-scattered-kernel-spaces`,
(a) ⇔ (b), and (b) says that `MP(H)`, the set of `N` satisfying (M) and (P),
is countable for every `H` satisfying (F). Suppose `H` is only of type FP_2
and has uncountably many `N` satisfying (M) and (P). Then each `H/N` is of
type FP_2 by consequence 1 of
`fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup`, and the counting
step of Section 3 of `simple-fp2-countability-iff-scattered-kernel-spaces-proof`
gives uncountably many simple FP_2 types. So
in (F), "finitely presented" and "of type FP_2" give the same statement.

**Witness 1 (drop M).**

1. By `constructed-continuum-of-finitely-generated-groups` there is a family of
   `2^aleph_0` pairwise non-isomorphic finitely generated groups.
2. By `every-countable-group-embeds-in-an-fp2-group`, each of them embeds in a
   group of type FP_2. An FP_2 group is finitely generated, hence countable, so
   it has only countably many finitely generated subgroups. Therefore the
   envelopes realize uncountably many isomorphism types of FP_2 groups.
3. By `fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup`, each envelope
   is `H_i/N_i` with `H_i` finitely presented and `N_i` perfect. There are
   countably many finitely presented groups up to isomorphism, so one `H`
   occurs for uncountably many pairwise non-isomorphic envelopes.
4. Transport the kernels into `H`. Non-isomorphic quotients have distinct
   kernels, which gives uncountably many perfect normal subgroups of `H`.

**Witness 2 (drop P).** `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels`
gives a finitely presented, torsion-free, hyperbolic Kazhdan `H` with
`2^aleph_0` normal `M_i` and pairwise non-isomorphic infinite simple quotients
`H/M_i`. A normal subgroup with nontrivial simple quotient is maximal. So
(M)+(F) hold for an uncountable family.

**Witness 3 (drop F).** By `v-times-shift-alternating-group-restrictions-are-simple`:

- `A(G)` is finitely generated (items 2–5 there);
- for every infinite minimal subshift `Y`, the restriction `ρ_Y` is onto a
  nontrivial simple group;
- distinct minimal subshifts give distinct kernels `K_Y`;
- there are `2^aleph_0` such `Y`.

By `v-times-shift-restriction-kernels-are-perfect`, every `K_Y` is perfect.
So `{K_Y}` is an uncountable family satisfying (M)+(P) in a finitely generated
group.

**Obstruction.** Let `I` be an invariant with countably many values on the
normal subgroups of finitely generated groups. Suppose a proof shows `I` is
injective on every `𝒩` satisfying some two of the hypotheses. On the witness
for the missing hypothesis, `𝒩` is uncountable, so `I` is not injective
there. So the proof's injectivity step cannot be valid. This is a pigeonhole
statement, and it covers each of the listed invariants.

- **Finite normal generators.** In witness 2 no member is finitely normally
  generated (item 4 of that claim).
- **r.e. indices.** An argument using only (M) plus recursive enumerability
  would give countability on witness 2 without reading (P). That is false,
  since witness 2 is uncountable.
- **Chabauty isolation.** In witness 3, `MP(A(G))` is uncountable, and it is
  `G_δ` in `N(A(G))` by Section 1 of
  `simple-fp2-countability-iff-scattered-kernel-spaces-proof`, which only uses
  finite generation. So by the perfect-set lemma there, it contains a Cantor
  set, and no isolation or Cantor–Bendixson argument using only finite
  generation can make it countable.

**(T1).** Suppose `A(G)` is of type FP_2. By witness 3 and consequence 1 of
`fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup`, every
`A(G)/K_Y = A(G|_{C×Y})` is a simple group of type FP_2. `A(G)` is finitely
generated, so each isomorphism type occurs for at most countably many `Y`.
Hence the target fails. Contrapositive: the target implies that `A(G)` is not
of type FP_2. A finitely presented group is of type FP_2, so `A(G)` is not
finitely presented either.

**(T2).** Item (e) of `simple-fp2-countability-iff-scattered-kernel-spaces` is
equivalent to the target. Its kernel criterion (item 3) says that `H/M` is
FP_2 iff `M = ⟨⟨F⟩⟩[M,M]` for some finite `F`, that is, iff `M/⟨⟨F⟩⟩` is
perfect. `∎`
