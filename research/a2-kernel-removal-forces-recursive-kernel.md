---
rg: 2
id: a2-kernel-removal-forces-recursive-kernel
kind: claim
title: A type [A_2] pair whose kernel can be removed by a sharp embedding has a recursive kernel, and for the Theorem C actor of a simple group this forces recursive one-variable mixed identities
distinct_from:
  finite-bi-index-subgroups-have-decidable-membership: that decides membership in a finite bi-index subgroup of a group with solvable word problem; this uses only finite presentation of the actor to make its action computable, and draws a consequence for the kernel and for FFWZ Question 5.9.
  abstract-btb-simple-quotient-fp-gate: that equates finite presentation of the simple quotient of an abstract twisted Brin-Thompson group with finite presentation of the action image; this is a computability condition on the kernel that every kernel-removing sharp embedding needs.
  boone-higman-implies-relative-permutational-bh: that places every Boone-Higman group sharply inside a type [A_2] actor; this says when the kernel of such an actor cannot be removed, in terms of the mixed identities of the simple group used.
  a2-action-with-non-finitely-presented-image: that is an explicit action whose image is not finitely presented but whose kernel is recursive and removable; this is the necessary condition a non-removable kernel would have to violate.
artifacts:
  - research/artifacts/bh-type-a-actions-2026-09-12.md
---

**ESTABLISHED** by `a2-kernel-removal-recursive-kernel-proof`.

Type `[A_2]` is as in Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687:
- `G` is finitely presented;
- point stabilizers are finitely generated;
- there are finitely many orbits on `S x S`.

The action need not be faithful. Sharp embeddings of normal pairs are as in their
Definition 1.6.

**(a) The action is computable.** Let `G` act on `S` with type `[A_2]` and
kernel `K`. Fix the finite data: orbit representatives, finite generating sets
of their stabilizers, and double-coset representatives. With that data:
- membership in each point stabilizer is decidable;
- the action is computable;
- `K` is co-recursively enumerable, so `G/K` has co-r.e. word problem.

Only finite presentation of `G` is used, not a solvable word problem.

**(b) Removable kernels are recursive.** Suppose `(G, K)` sharply embeds in
`(G', K')` for a type `[A_2]` action of `G'` with `K'` finitely normally
generated in `G'`. Then `K` is recursive: `G/K` has solvable word problem.

**(c) The Theorem C actor.** Let `Γ` be an infinite finitely presented simple
group and `n >= 2`. Let `A = Aut_Γ(Γ * F_n)` act by precomposition on
`X = Hom_Γ(Γ * F_n, Γ)`, with kernel `K`. This is the type `[A_2]` action of
FFWZ's proof of Theorem 5.1.

Let `J_1(Γ) ⊆ Γ * <y>` be the words `w` with `w(g) = 1` for every `g in Γ`: the
one-variable mixed identities. Then `J_1(Γ)` is co-r.e., and it many-one reduces
to `K`. So if `J_1(Γ)` is not recursive:
- `K` is not recursive;
- `A/K` is not recursively presented, hence not finitely presented (another
  instance of FFWZ Question 5.8);
- `(A, K)` sharply embeds in no type `[A_2]` pair with finitely normally
  generated kernel.

**Consequence for Question 5.9.** A positive answer to the first part of FFWZ
Question 5.9 (`a2-pairs-embed-in-a2-pairs-with-fng-kernels`) forces a recursive
set of one-variable mixed identities for every infinite finitely presented
simple group. For MIF groups that set is just the words trivial in `Γ * <y>`,
which is recursive.

**Not claimed.**
- **No example.** No finitely presented simple group with a non-recursive set of
  mixed identities is exhibited.
- **Not sufficient.** A recursive kernel is not shown to allow removal.
