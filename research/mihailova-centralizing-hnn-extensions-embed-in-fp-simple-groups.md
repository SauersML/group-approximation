---
rg: 2
id: mihailova-centralizing-hnn-extensions-embed-in-fp-simple-groups
kind: claim
title: Centralizing HNN extensions of F_m x F_m along Mihailova subgroups of decidable finite presentations embed in finitely presented simple groups (MH)
distinct_from:
  bh-embeddability-survives-decidable-edge-hnn: that is HNN permanence for every finitely generated edge with decidable membership; this is the single family A = F_m x F_m, C = M(Q) that the finite-presentation index-set question needs.
  fp-embeddability-index-set-is-sigma-3-complete: that is the index-set statement; this is the hypothesis MH that implies it.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that asks for finitely presented simple groups with word problems beyond every recursive time bound; this claim implies it, so it is at least as hard.
---

**OPEN (MH).** Let `Q = ⟨X | R⟩` be a finite presentation with `|X| = m ≥ 2` and
solvable word problem. Let `M(Q) = {(u,v) ∈ F_X × F_X : u =_Q v}`. Then
`H(Q) = ⟨F_X × F_X, s | [s, c] = 1 (c ∈ M(Q))⟩` embeds in a finitely presented
simple group.

## What is proved about MH (lane proofs, not reviewed)

1. **Position.**
   - MH follows from `boone-higman-conjecture`, since `H(Q)` is finitely presented
     with decidable word problem.
   - MH also follows from `bh-embeddability-survives-decidable-edge-hnn`, with
     `A = F_m × F_m ≤ V`.
   - MH implies `fp-embeddability-index-set-is-sigma-3-complete`.
2. **Structure.** Write `N = ⟨⟨R⟩⟩ ⊴ F = F_X`. Then
   `H(Q) ≅ L ⋊ F`.
   - Here `L = ⟨F, s | [s, n] = 1 (n ∈ N)⟩ = F *_N (N × ⟨s⟩)`.
   - `F` acts on `L` by conjugation on `F` and trivially on `s`.
   - The proof: use the generators `(x,1)` and `(x,x)`. The group `F × F` equals
     `F_1 ⋊ Δ`, where the diagonal `Δ` acts on `F_1` by inner automorphisms. Then
     `[s, Δ] = 1` together with `[s, R] = 1` yields `[s, N] = 1`.
3. **Not obviously as strong as Boone–Higman.** `H(Q)` is torsion-free: it is an
   HNN extension of a torsion-free group. So `Q ⊄ H(Q)` whenever `Q` has torsion,
   and MH gives no embedding of `Q` itself.
4. **MH implies `fp-simple-groups-with-arbitrarily-complex-word-problem`.**
   - **A hard `Q`.** Fix a recursive `T`. Take a unary set `A`, computable but not
     decidable in time `T(Ck)` for any constant `C`. Its Miller amalgam `G_A` has
     test words of length `O(k)`. Let `Q` be a finitely presented Clapham
     overgroup of `G_A` with solvable word problem.
   - **The linear chain.** Each step of
     `A ≤ WP(G_A) ≤ WP(Q) ≤ WP(H(Q)) ≤ WP(S)` is a linear-size reduction:
     - `G_A` is a finitely generated subgroup of `Q`;
     - `u =_Q 1` iff `[s,(u,1)] = 1`, by Britton's lemma;
     - `S` is any finitely presented simple group containing `H(Q)`.
   - **Conclusion.** So `S` has word problem beyond `T`.

## Consequence for attacks

No fixed host can realize every `H(Q)`. That includes `DV_F`, whose word problem
is the orbit problem of `F`, and every `nV`. An element `s` commuting exactly with
`M(Q)` must live in a host whose word problem is at least as hard as `Q`'s, so
the host has to depend on `Q`. The finite-presentation index-set question uses
only the `Q_i` coming from cofinite `U_i`. An attack avoiding this barrier needs a
uniform finitely presented family whose cofinite members have uniformly bounded
word-problem complexity. The recursively presented family does have this property:
all its cofinite members lie in `DV_F`.
