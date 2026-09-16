---
rg: 2
id: a2-kernel-recursion-ascends-normal-orbit-finite-chains
kind: claim
title: Kernel membership for a type [A_2] action is certified by commutation with orbit-finite subgroups, so kernel recursion ascends normal chains and every normalizer cover has a recursive kernel
distinct_from:
  a2-action-kernels-are-recursive: that asserts a recursive kernel for every type [A_2] action; this proves it for actions with a subnormal chain of finitely generated orbit-finite subgroups whose bottom meets the kernel in an r.e. set, and for kernels centralizing conjugates of finitely many orbit-finite subgroups.
  a2-kernel-removal-forces-recursive-kernel: that proves every kernel is co-r.e. and every removable kernel is recursive; this proves kernels r.e., hence recursive, from certificates of commutation, with no removal hypothesis.
  a2-stabilizer-image-presentation-controls-kernel: that ties recursion of the kernel to presentations of the action image and of stabilizer images; this derives recursion from normal chains of orbit-finite subgroups and from exact commutation.
  normalizer-extension-of-type-a-actor-is-a2-cover: that builds the normalizer covers and computes their kernels and images; this proves those kernels recursive, so the images have solvable word problem.
---

**ESTABLISHED** by `a2-kernel-recursion-ascends-normal-orbit-finite-chains-proof`.

**Setting.** Let `G ↷ S` be of type `[A_2]` as in
`a2-kernel-removal-forces-recursive-kernel`:
- `G` is finitely presented;
- point stabilizers are finitely generated;
- there are finitely many orbits on `S x S`.

Let `K` be the kernel. Fix a finite generating set of `G` and orbit representatives
`x_1, ..., x_p`. Encode a point `c.x_i` by the word `c` and the index `i`.

A set of elements of `G` is *r.e.* if the set of words representing its elements is
recursively enumerable, and likewise for *recursive*. A subgroup `M <= G` is
*orbit-finite* if it has finitely many orbits on `S`.

**(1) Certificates.** Suppose we are given:
- `W`, an r.e. set of words;
- `K_0 ⊆ K`, an r.e. subset;
- `C`, an r.e. set of pairs `(A, Y)`, where `A` is a finite set of words, `Y` is a
  finite set of encoded points, and `<A>.Y = S` for every pair.

Assume that for every `w in W` representing an element of `K` there is some
`(A, Y) in C` with `[w, a] in K_0` for all `a in A`. Then the words of `W` that
represent elements of `K` form an r.e. set.

**(2) Ascent along normal chains.** Let `N_0 ⊴ N_1 ⊴ ... ⊴ N_k = G` be finitely
generated subgroups, with `N_0` orbit-finite. Then `K` is recursive if and only if
`N_0 ∩ K` is r.e.

In particular, `K` is recursive in each of these cases:
- `N_0 ∩ K = 1`;
- `N_0 ⊴ G`, and the kernel of `N_0 ↷ S` is recursive as a set of words in the
  generators of `N_0`.

**(3) Exact centralizers.** Let `M_1, ..., M_q <= G` be finitely generated and
orbit-finite. Suppose every element of `K` commutes, in `G`, with every element of
`h M_j h^-1` for some `h in G` and some `j`. Then `K` is recursive.

**(4) Normalizer covers.** Every type `[A_2]` action
`G~ = Γ x|_θ F_m ↷ Ω` of `normalizer-extension-of-type-a-actor-is-a2-cover` has a
recursive kernel. So for every finitely presented permutation group `Γ <= Sym(Ω)`
with finitely many orbits on `Ω x Ω` and finitely generated point stabilizers, and
every finitely generated `Q <= N_(Sym(Ω))(Γ)`, the group `ΓQ` has solvable word
problem.

**(5) Constraint on counterexamples.** Suppose `K` is not recursive. Then:
- every finitely generated orbit-finite `N_0` that starts a finitely generated normal
  chain up to `G` meets `K` in a set that is not r.e.;
- in particular no finitely generated orbit-finite normal subgroup of `G` meets `K`
  trivially;
- for any finite family of finitely generated orbit-finite subgroups, some element of
  `K` centralizes no conjugate of any member of the family.
