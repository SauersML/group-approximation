---
rg: 2
id: pbh-finite-edge-closure-equivalences
kind: claim
title: For the permutational Boone--Higman class, closure under finite-edge amalgams, finite-edge HNN extensions, finite-edge graphs of groups, conjugacy realization of finite subgroups, and index-two finite overgroup extension are all equivalent
distinct_from:
  pbh-closed-under-finite-edge-graphs-of-groups: that is the open closure itself; this proves that its five natural forms are equivalent.
  pbh-coset-wreaths-iff-identity-edge-hnns: that is the analogous equivalence for identity edges over arbitrary subgroups (centralizer realization); this is the one for twisted edges over finite subgroups (conjugacy realization).
  free-permutational-products-preserve-pbh: that proves the centralizing case and the reductions of amalgams and HNN extensions to a common or conjugating overgroup; this closes the circle between all finite-edge forms.
---

**ESTABLISHED** by `pbh-finite-edge-closure-equivalences-proof` (lane proof, not reviewed;
no priority claimed). The following are equivalent.

1. **Amalgams.** `X *_C Y ∈ B_A` for all `X, Y ∈ B_A` and every finite group `C`
   embedded in both.
2. **HNN extensions.** `G*_θ ∈ B_A` for all `G ∈ B_A` and every isomorphism `θ` between
   finite subgroups of `G`.
3. **Graphs of groups.** The fundamental group of every finite graph of groups with vertex
   groups in `B_A` and finite edge groups lies in `B_A`.
4. **Conjugacy realization.** For `G ∈ B_A` and an isomorphism `θ: C_1 -> C_2` of finite
   subgroups, some `L ∈ B_A` contains `G` and an element `s` with `s c s^(-1) = θ(c)` for
   all `c ∈ C_1`.
5. **Involutive extension.** For `H ∈ B_A`, commuting finite subgroups `A_1, A_2 ≤ H`
   with `A_1 ∩ A_2 = 1`, and an isomorphism `θ: A_1 -> A_2`,
   `H *_(A_1 × A_2) (A_1 × A_2) ⋊ ⟨e⟩ ∈ B_A`. Here `e` has order 2 and acts by
   `(a, b) -> (θ^(-1)(b), θ(a))`. The extension is the wreath product `A_1 wr Z/2`.

## Why this form matters

- **One gluing move.** Form 5 involves a single involution acting on a finite group
  `A × A`. So the whole finite-edge theory of `B_A` reduces to extending one finite
  subgroup of shape `A × A` by its swap. The general form "`H *_F E` for all finite
  `E ⊇ F`" is a special case of form 1, so it is equivalent too.
- **Known cases.** Forms 1–4 hold when:
  - the edge groups are centralized (`free-permutational-products-preserve-pbh`, Part 3);
  - the vertex groups sit in one full Cantor host with matching strata
    (`finite-edge-graphs-of-full-cantor-subgroups-lie-in-b-a`);
  - some finite quotient of `G` is injective on `C_1 ∪ C_2`. Then a finite-index subgroup
    of `G*_θ` acts freely on the edges of its Bass–Serre tree, so it is a free product of
    subgroups of `G` and a free group. Finite-index overgroup closure then applies.

## Lesson for general BH

Every combination question for `B_A` reduces to a realization question inside one
overgroup:
- identity edges become centralizers (`pbh-coset-wreaths-iff-identity-edge-hnns`);
- twisted finite edges become conjugacy (this node);
- conjugacy reduces to one swap of `A × A`.

Tower routes to Boone--Higman, which build hosts by HNN extensions, need exactly these
realization moves and nothing more. The actor theory (Theorems C and E) never has to be
reopened.
