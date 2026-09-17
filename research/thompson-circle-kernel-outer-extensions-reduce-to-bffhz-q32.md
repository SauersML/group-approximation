---
rg: 2
id: thompson-circle-kernel-outer-extensions-reduce-to-bffhz-q32
kind: claim
title: For a finitely presented simple Higman--Thompson circle kernel S, a positive answer to BFFHZ Question 3.2 for S puts every outer extension of S by a finitely presented group in the permutational Boone--Higman class
distinct_from:
  outer-extensions-of-fp-simple-mif-groups-satisfy-pbh: that proves the outer-extension statement unconditionally for MIF kernels, where the action kernel is S itself; this treats the non-MIF circle kernels, where the action kernel is unknown, and is conditional on BFFHZ Question 3.2 for the kernel.
  bffhz-action-image-is-finitely-presented: that is the refuted universal upgrade of Question 3.2 to computably presented cores; this assumes the published question only for one finitely presented non-MIF kernel and derives finite presentation of the enlarged actor by Aut(S).
  normalizer-image-of-type-a-actor-is-type-a: that enlarges a faithful type (A) actor by normalizing permutations; this starts from a type [A_2] actor whose kernel is not trivial and has to control the ρ-image of that kernel, which is the word-automorphism input.
  micro-supported-word-automorphisms-are-pointwise-inner: that is the lemma on word automorphisms; this is its consequence for type (A) actors and outer extensions.
---

**ESTABLISHED** by `thompson-circle-kernel-outer-extensions-bffhz-q32-proof`.
Not independently reviewed.

## Statement

Let `T = T_{n,r_0}` (`n >= 2`, `r_0 >= 1`). Let `S` satisfy `[T,T] <= S <= T`, and
assume `S` is finitely presented and simple. For example, `S = T` for `n = 2`,
`r_0 = 1`. Fix `m >= 2`. Let:
- `A = Aut_S(S * F_m)` act on `X = Hom_S(S * F_m, S)` by precomposition;
- `K_A` be the kernel of this action.

Suppose `A/K_A` is finitely presented. This is BFFHZ Question 3.2 for `S` and `m`.

1. Every `B` with `Inn(S) <= B <= Aut(S)` and `B/Inn(S)` finitely presented lies in
   `B_A`.
2. Consider an exact sequence `1 -> S -> I -> Q -> 1` with `Q` finitely presented
   and `Q -> Out(S)` injective. Then `I ∈ B_A`. So every finitely generated subgroup
   of `I` has solvable word problem and embeds in a finitely presented simple group.

**Contrapositive for the target.** Let `G` be a finitely generated decidable group
that embeds in such an `I` but not in `B_A`. Then BFFHZ Question 3.2 has a negative
answer for `S`, for every `m >= 2`.

## What changes

`research/artifacts/outer-extensions-mif-pbh-2026-09-16.md`, §8, left two
independent holes for non-MIF kernels:
- (a) Question 3.2 for `S`;
- (b) finite normal generation of `W/Inn(S)`.

For the Thompson circle kernels, (b) is now proved for every `B`, by
`micro-supported-word-automorphisms-are-pointwise-inner`. So the non-MIF
outer-extension problem for these kernels has exactly one prerequisite left, and it
is the published question. BFFHZ single this case out: "it is unclear what to
expect, even for example for Thompson's group T".

Note the relevance of infinite outer automorphism groups. Olukoya
(arXiv:1908.03816, abstract) shows `Out(T_{n,r})` is infinite for `n > 2` and
contains Thompson's `F`. So item 1 is not vacuous beyond finite-index overgroups
whenever the simple kernel `S` inherits such outer automorphisms. This transfer
from `Out(T_{n,r})` to `Out(S)` was not checked.

## Not claimed

- **Question 3.2.** No answer is given, even for `T`.
- **Other non-MIF kernels.** Kernels that are not PL circle groups are not
  covered; see the "Not claimed" part of the lemma.
- **No universality.** Fixed kernels of bounded word-problem complexity cannot be
  universal hosts (target, Attempt 1). This node is about separating the target from
  pBH group by group, not about proving the target.
