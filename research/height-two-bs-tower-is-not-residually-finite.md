---
rg: 2
id: height-two-bs-tower-is-not-residually-finite
kind: claim
title: The height-two Baumslag--Solitar tower <a_0,a_1,a_2 | a_1 a_0 a_1^-1 = a_0^2, a_2 a_1 a_2^-1 = a_1^2> is not residually finite; the commutator of a_0 with its conjugate by a square root of a_1 dies in every finite quotient
distinct_from:
  baumslag-solitar-towers-have-no-faithful-linear-image: that shows a_0 has finite order in every linear image of the tower; this exhibits a nontrivial element of the tower that dies in every finite image, a different element and a different reason (profinite density of the base in Z[1/2]).
  baumslag-gersten-group-is-neither-linear-nor-self-similar: that shows every finite image of the Baumslag--Gersten group kills a, using the stable letter t; this shows the failure of residual finiteness already inside the tower subgroup, with no stable letter.
  baumslag-gersten-splits-over-bs12-edges: that makes the tower the vertex group of a splitting of BG; this records that this vertex group is itself non-residually-finite.
---

**ESTABLISHED** (elementary; no novelty claimed; not yet refereed).

## Statement

Let `K = ⟨a_0, a_1, a_2 | a_1 a_0 a_1^-1 = a_0^2, a_2 a_1 a_2^-1 = a_1^2⟩`. Put
`h = a_2^-1 a_1 a_2`, a square root of `a_1`, and `w_0 = h a_0 h^-1`. Then:
1. `[w_0, a_0] ≠ 1` in `K`;
2. `φ([w_0, a_0]) = 1` for every homomorphism `φ` from `K` to a finite group.

So `K` is not residually finite. It is the subgroup `⟨a, tat^-1, t^2at^-2⟩` of the Baumslag--Gersten
group, the vertex group of `baumslag-gersten-splits-over-bs12-edges`.

## Why it matters

- **Hosts.** The finite residual of `K` is nontrivial with no stable letter. So a host for `K` must
  already avoid the profinite engines: residually finite, linear and self-similar hosts, and
  hosts in which `K` has compact closure.
- **The one-relator problem.** Any Boone--Higman host for `BG`, and so any solution of
  `one-relator-groups-satisfy-boone-higman`, contains a host for `K`. Whether `K` embeds in a
  finitely presented simple group is not settled on this graph. It is a smaller test case than
  `BG`: three generators, two relators, and no stable letter.

## Proof

`K = B_0 *_C B_1` with `B_0 = ⟨a_0, a_1⟩`, `B_1 = ⟨a_1, a_2⟩`, both `≅ BS(1,2)`, and
`C = ⟨a_1⟩`. In `B_1`, `a_1` generates the base `A_1 = ⟨⟨a_1⟩⟩ ≅ Z[1/2]`, and `h ∈ A_1` is the
element `1/2`.

**Item 1.** `h ∉ C`, because `1/2 ∉ Z`. `a_0 ∉ C`, because `a_0` lies in the normal base of `B_0`,
which meets `C` trivially. So
`[w_0, a_0] = h · a_0 · h^-1 · a_0 · h · a_0^-1 · h^-1 · a_0^-1`
is a word of eight syllables alternating between `B_1 ∖ C` and `B_0 ∖ C`. By the normal form
theorem for amalgams, it is not `1`.

**Item 2.**
- *Odd order.* In `φ(B_1)`, `φ(a_1)` is conjugate to its square, so it has odd order.
- *The base is cyclic.* `φ(A_1)` is a finite quotient of the 2-divisible group `Z[1/2]`, so it has
  odd order. Its element `φ(1/2^k)` is `2^-k φ(a_1)`, computed in that odd-order group, so
  `φ(A_1) = ⟨φ(a_1)⟩`.
- *Conclusion.* Hence `φ(h) = φ(a_1)^j` for some `j ≥ 0`. In `B_0`,
  `a_1^j a_0 a_1^-j = a_0^(2^j)`, so `φ(w_0) = φ(a_0)^(2^j)` commutes with `φ(a_0)`. `∎`
