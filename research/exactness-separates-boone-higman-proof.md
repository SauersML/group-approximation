---
rg: 2
id: exactness-separates-boone-higman-proof
kind: route
title: Feed the decidable residually finite non-exact group into the hereditary separator and into every exact host
target: exactness-separates-boone-higman-iff-fp-simple-groups-exact
requires: [decidable-residually-finite-non-exact-group-exists, hereditary-approximation-disproofs-of-boone-higman, exact-groups-are-closed-under-extensions, commutative-ring-linear-groups-have-property-a]
artifacts:
  - research/artifacts/exactness-boone-higman-separator-2026-09-17.md
---

Write `fps` for the class of finitely presented simple groups and `Ex` for the class of countable exact groups.

## 0. Heredity

- Closed subgroups of exact groups are exact (`exact-groups-are-closed-under-extensions`, Kirchberg--Wassermann).
- For countable discrete groups, exactness is equivalent to property A (Osajda arXiv:1406.5015 l.166, quoted in `research/artifacts/sk-free-1-exactness-2026-09-13-part1.md` §3).
- Property A passes to subgroups (Willett arXiv:math/0612492 l.1607) and to coarsely embedded spaces (l.540–542), quoted in the artifact §1.2.

So `Ex` is closed under isomorphism and subgroups, and the framework of `hereditary-approximation-disproofs-of-boone-higman` (Theorem 1) applies to it.

## 1. Separation

By `decidable-residually-finite-non-exact-group-exists`, there is a finitely generated residually finite group `G` with solvable word problem and `G ∉ Ex`. So (S2) holds, and `Ex` separates iff (S1) holds, that is, iff `fps ⊆ Ex`. By Theorem 1 of the hereditary node, separation refutes `boone-higman-conjecture`.

Contrapositive: suppose the conjecture holds.
- Take the non-exact decidable simple Kazhdan LEF group `H` of item 2 of the witness node.
- The conjecture gives `H ≤ K` with `K ∈ fps`.
- `K ∉ Ex` by heredity.

∎

## 2. Class kill

Let every member of `C` be exact. Suppose every decidable input, or every residually finite decidable input, or every decidable simple Kazhdan LEF group, embedded in some member `M` of `C`.
- Apply this to `G`, respectively `H`.
- Heredity gives `G ∈ Ex`, respectively `H ∈ Ex`. That contradicts the witness node.

The two enlargements of `C` are harmless:
- **Extensions of members by members** are exact by Kirchberg--Wassermann.
- **Coarse embeddings.** If `M` merely coarsely embeds in a property-A space, `M` has property A (l.540–542), and `G ≤ M` has it by l.1607.

∎

## 3. Instances

- **Linear over a commutative ring.** Countable subgroups of `GL_n(R)` have property A (`commutative-ring-linear-groups-have-property-a`).
- **Hyperbolic groups; proper cocompact actions on finite dimensional CAT(0) cube complexes; finite asymptotic dimension; discrete subgroups of connected Lie groups.** These come from Willett's list, l.1963–1980 and l.1451, quoted in the artifact §1.2. They are secondary citations of Roe, Campbell--Niblo and Anantharaman-Delaroche--Renault. The primaries were not re-read, and the kill for these classes is only as good as those imports.
- **Products of locally finite trees.** Let `Γ` act properly cocompactly on `T_1 × T_2`.
  - The Švarc--Milnor lemma (classical, not quoted) makes `Γ` coarsely equivalent to `V(T_1) × V(T_2)` with the `ℓ^1` metric.
  - That space has property A by Willett l.1136 (trees) and l.1310–1317 (products).
  - Property A is a coarse invariant (l.494).
  - Alternatively, `T_1 × T_2` is a two-dimensional CAT(0) square complex, and the previous instance applies.

## 4. Orthogonality

`G` is residually finite, hence LEF, sofic and hyperlinear (classical, as recorded in `hereditary-approximation-disproofs-of-boone-higman` Theorem 2). So the soficity and hyperlinearity separators cannot use `G` as their (S2) witness, while exactness can. The exactness separator is not the same statement as those separators: its decidable side is settled, and theirs is not. ∎
