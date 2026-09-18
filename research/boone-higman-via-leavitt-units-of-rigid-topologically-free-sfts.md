---
rg: 2
id: boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts
kind: route
title: Put the group inside the acting group of a finitely presented minimal topologically free crossed product with torsion-free isotropy, then pass to the units of its Leavitt tensor
target: boone-higman-conjecture
requires:
  - decidable-groups-lie-in-fp-topologically-free-crossed-products
  - free-minimal-cantor-crossed-products-are-central-simple
  - torsion-free-isotropy-leavitt-tensor-hosts-have-trivial-k1-k2
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - central-simple-leavitt-tensor-unit-groups-are-simple
---

**Route** (lane bh-g3-topfree, 2026-09-18). This is `boone-higman-via-leavitt-units-of-rigid-sft-overgroups`
with (E) and (K) weakened to (E′) and (K′). The step-by-step justification is
`master-route-needs-only-topological-freeness`, item (1).

Let `G` be finitely generated with solvable word problem, and `L = L_(F_2)(1,2)`.

1. By (E′) choose a finitely generated `Λ >= G` and a nonempty subshift `X`. The action is minimal and
   topologically free, every finite subgroup acts freely, and `B = LC(X, F_2) ⋊ Λ` is finitely
   presented. `G` is infinite without loss of generality, so `X` is a Cantor space.
2. `free-minimal-cantor-crossed-products-are-central-simple` (minimal and topologically free) makes `B`
   simple with `Z(B) = F_2`.
3. `G ≤ Λ ≤ B^x ≤ (B ⊗ L)^x`. `λ ↦ u_λ` is injective because `X ≠ ∅`, and `b ↦ b ⊗ 1` is a unital
   injection.
4. (K′) gives `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`.
5. `leavitt-tensor-hosts-acyclic-steinberg-and-fp`(3) makes `(B ⊗ L)^x` finitely presented. This is
   conditional on the Khanh import, which bh-free-26 audited at source in
   `khanh-ara-cortinas-hypotheses-hold-for-leavitt-tensor-hosts`.
6. `central-simple-leavitt-tensor-unit-groups-are-simple`(2) makes `(B ⊗ L)^x` simple.

So `G` embeds in a finitely presented simple group. ∎

## Status

**OPEN**, through (E′) and (K′). Steps 2, 5 and 6 are established (unreviewed; step 5 conditional on
Khanh). (E) ⇒ (E′) and (K′) ⇒ (K), so this route is implied by the free version's premises, and it
asks strictly less of the dynamics.

- **Where decidability is consumed.** The sufficient form of (E′), a quantum-rigid minimal
  topologically free SFT over an fp overgroup, forces solvable word problem on its own
  (`rigid-topologically-free-sfts-force-solvable-word-problem`).
- **K-gate.** (K′) is a Farrell–Jones instance for the acting group; it is not a new difficulty
  created by the relaxation.

## Lesson for general BH

The ring-side master route needs an effective minimal action, not a free one. Its dynamical crux is
therefore (★′): rigidity plus topological freeness over an fp overgroup of the input. That admits
compression-rigid boundary codings, which over non-amenable groups are the only rigid mechanism found
so far.
