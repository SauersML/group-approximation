---
rg: 2
id: free-kernel-extensions-stay-in-the-permutational-class
kind: claim
title: An extension of a group in B_A by a finitely generated free group of rank at least 2 lies in B_A, and so do iterated such extensions and fundamental groups of free-fibred bundles over aspherical bases
distinct_from:
  pbh-class-closed-under-relative-holomorphs: that embeds the specific holomorphs (M * F_m) ⋊ Aut_M(M * F_m) in a relative automorphism group; this is closure under every extension with finitely generated free kernel, whatever the quotient in B_A and whatever the action.
  free-by-virtually-free-groups-satisfy-boone-higman: that reaches free-by-(virtually free) groups through BLIW generalized Baumslag--Solitar witnesses, which need a virtually free quotient; this allows any quotient in B_A, e.g. Z^2, a linear group, Aut(F_n), or a braid group.
  b-tilde-artin-pbh-via-free-fibre-kernel-proof: that uses the same centreless-kernel embedding once, inside the B̃_n argument; this isolates it as a permanence theorem for the class.
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure under subgroups, finite direct products and finite-index overgroups; this is closure under infinite extensions with free kernel.
artifacts:
  - research/artifacts/gq-bh-bh-verify-artin-euclidean-toric.md
---

**ESTABLISHED** through `free-kernel-extensions-stay-in-the-permutational-class-proof`.
This is a lane proof, elementary, and not independently reviewed. No priority is
claimed: the embedding `G -> Aut(K) × G/K` is classical, and the only input here is
BFFHZ's theorem that `Aut(F_r)` is in `B_A`.

`B_A` is the class of groups that embed in a group admitting an action of type (A)
(`boone-higman-type-a-class-closed-under-finite-extensions`). Every member embeds in a
finitely presented simple group and, if finitely generated, has solvable word problem
(`type-a-action-gives-boone-higman-for-subgroups`).

## Statement

1. **Free kernels.** Let `1 -> K -> G -> Q -> 1` be exact, with `K` free of finite
   rank `r >= 2` and `Q ∈ B_A`. Then `G ∈ B_A`.
2. **Centreless kernels.** More generally, the same holds when `K` has trivial centre
   and `Aut(K) ∈ B_A`. For example, `K` can be a finite direct product of free groups
   of finite ranks `>= 2`.
3. **Iterated extensions.** Let `G = G_m -> G_(m-1) -> ... -> G_0` be surjections
   such that every kernel is free of finite rank `>= 2`, and let `G_0 ∈ B_A`. Then
   `G ∈ B_A`.
4. **Bundles.** Let `F -> E -> B` be a locally trivial fibre bundle of connected
   spaces with `π_2(B) = 0`, `π_1(F)` free of finite rank `>= 2`, and
   `π_1(B) ∈ B_A`. Then `π_1(E) ∈ B_A`.

The groups `G` need not be finitely generated. When `G` is finitely generated, it
embeds in a finitely presented simple group.

## Examples

- Every extension of `F_r` (`r >= 2`) by `Z^k`, by a finitely generated linear group
  in any characteristic (`finitely-generated-linear-groups-satisfy-boone-higman`,
  whose permutational form is established in characteristic zero), by `Aut(F_n)`, or
  by a braid group. The board of lane bh-free-extensions records free-by-`Z^2` as
  outside every BLIW class; it is covered here.
- Fundamental groups of fibre-type toric and elliptic arrangement complements
  (`fiber-type-toric-arrangement-groups-lie-in-the-pbh-class`).
- The B̃_n argument (`b-tilde-artin-pbh-via-free-fibre-kernel-proof`, steps 4–5) is
  part 4 applied to the Li--Roushon bundle.

## Scope

- **Rank one.** Kernels `K ≅ Z` are not covered: `Z` is not centreless, and
  `Z`-by-`Q` extensions include central extensions such as the Heisenberg group over a
  quotient, which need separate arguments.
- **Surface kernels.** Closed-surface kernels are not covered, because it is open
  whether `Aut(π_1 Σ_g)` (the extended mapping class group of a closed surface) lies in
  `B_A`.
