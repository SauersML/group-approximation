---
rg: 2
id: thompson-t-relative-automorphism-actor-kernel-is-recursive
kind: claim
title: For n >= 2 the kernel of the action of Aut_T(T * F_n) on Hom_T(T * F_n, T) is recursive
distinct_from:
  a2-kernel-removal-forces-recursive-kernel: that shows a non-recursive set of mixed identities would make this kernel non-recursive and the pair non-removable; this proves the kernel recursive when the simple group is Thompson's group T.
  relative-automorphism-action-is-highly-transitive: that imports transitivity and finitely generated stabilizers for this action; this is a computability statement about its kernel for T.
  thompson-t-mixed-identity-problem-is-decidable: that decides mixed identities of T; this transfers the decision to the kernel of the relative automorphism actor.
artifacts:
  - research/artifacts/solve-mixed-identity-undecidable-2026-09-13.md
---

**ESTABLISHED** by `thompson-t-relative-automorphism-kernel-recursive-proof`.

**Statement.** Let `n >= 2` and `A = Aut_T(T * F_n)`, the automorphisms fixing
`T` pointwise. `A` acts by precomposition on `X = Hom_T(T * F_n, T)`. Let `K` be
the kernel. For any finite generating set of `A`, given by the images of
`x_1, ..., x_n` as words in `T * F_n`, membership in `K` is decidable. So `A/K`
has solvable word problem.

**Context.** BFFHZ (arXiv:2503.21882v2, extracted text on MSI, l.463–464) note
that this action "is never faithful" when `n >= 2` and `G` is not MIF, and `T`
is not MIF (`homeo-circle-three-arc-commutator-word-is-mixed-identity`). So `K`
is a nontrivial recursive normal subgroup.

**Consequences.**
- **FFWZ Question 5.9.** Attempt 2 of `a2-pairs-embed-in-a2-pairs-with-fng-kernels`
  asks for a Theorem C actor with non-recursive kernel. This one, for `T`, is not
  one.
- **BFFHZ Question 3.2 for `T`.** Its computability obstruction disappears.
  Finite presentation of `A/K` is still not decided.

**Not claimed.** Removability of `K` by a sharp embedding, and finite
presentation of `A/K`.
