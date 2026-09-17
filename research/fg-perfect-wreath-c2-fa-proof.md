---
rg: 2
id: fg-perfect-wreath-c2-fa-proof
kind: route
title: Commuting conjugate factors force each other's axes to be fixed, and perfectness kills the common axis
target: fg-perfect-wreath-c2-has-property-fa
requires: []
artifacts:
  - research/artifacts/fg-perfect-wreath-c2-fa-proof-2026-09-17.md
---

This restores the demoted attempt artifact
`research/artifacts/fg-perfect-wreath-c2-fa-proof-2026-09-17.md` after an
independent referee pass (2026-09-17, agent swarm-0917-w5-bh-wreath-fa). The
proof is written out again, with every tree fact justified.

**Tree facts** (Serre, *Trees*, Chapter I, §6). Trees are simplicial, and
actions are by automorphisms without inversions.
- **(F1)** An automorphism `g` is elliptic (it fixes a vertex) or hyperbolic.
  A hyperbolic `g` has a unique axis `L_g`, a line on which it translates by
  `l(g) > 0`. For every vertex `x`, `d(x, gx) = l(g) + 2 d(x, L_g)` (§6.4,
  Proposition 24). Hence `L_{b g b^-1} = b L_g`.
- **(F2)** A finitely generated group in which every element is elliptic fixes
  a vertex (§6.5, Corollary 3 of Proposition 26).
- **(F3)** The fixed set of a group that fixes a vertex is a subtree.
- **(F4)** A group with a bounded orbit fixes a vertex, or stabilizes an edge
  and then, without inversions, fixes its endpoints.

**Lemma (line automorphisms).** Let `g` preserve a line `L`. Then `g|_L` is a
translation by some `tau` or a reflection. A reflection fixes a vertex of `L`,
because a reflection about the midpoint of an edge would invert that edge. If
`tau != 0`, then `g` is hyperbolic with `L_g = L`. *Proof.* Suppose `g` fixes a
vertex `v`. Let `p` be the nearest-point projection of `v` to `L`. Since `g`
preserves `L` and fixes `v`, it fixes `p`, so `tau = 0`. So `g` is hyperbolic. On
`L` the displacement is `|tau|`, and by (F1) the points of minimal displacement
form `L_g`. A vertex off `L` has displacement `|tau| + 2 d(x, L)`, so it is not
minimal. Hence `L_g = L`. `□`

Let `W = (A_1 x A_2) ⋊ <sigma>` act on `T`, where `A_i` are the two copies of the
finitely generated perfect group `A`, `sigma A_1 sigma^-1 = A_2` and `N = A_1 A_2`.

**Step 1 (reduce to a factor).**
- If `N` fixes a vertex `v`, then `W v = N v ∪ sigma N v = {v, sigma v}`. This
  orbit is bounded, so `W` fixes a vertex by (F4).
- If `A_1` and `A_2` each fix a vertex, then `F = Fix(A_1)` is a subtree by (F3).
  It is `A_2`-invariant, since `A_2` commutes with `A_1`. Let `u` be fixed by
  `A_2`, and let `p` be its projection to `F`. For `b in A_2`, `b p` is the
  projection of `b u = u` to `b F = F`, so `b p = p`. So `N` fixes `p`.

Hence, if `W` fixes no vertex, some `A_i` fixes none. Conjugating by `sigma`,
neither does.

**Step 2 (a commuting factor fixes the axis).** Assume neither `A_i` fixes a
vertex.
1. By (F2), `A_1` contains a hyperbolic `h`. Put `L = L_h`.
2. Let `b in A_2`. Then `b L = L_{b h b^-1} = L`. If `b|_L` were a reflection
   `r`, then `h|_L = r h|_L r^-1 = (h|_L)^-1`, which is impossible for a nonzero
   translation. So `b` translates `L` by some `tau_b`.
3. Suppose `tau_b != 0` for some `b`. By the Lemma, `b` is hyperbolic with
   `L_b = L`. Let `h' in A_1` be any hyperbolic element. By item 2 with `h'` in
   place of `h`, `b` translates `L_{h'}`, and not by `0`, since `b` fixes no
   vertex. So `L_{h'} = L_b = L`.
4. For `g in A_1`, the element `g h g^-1` is hyperbolic and lies in `A_1`, so
   `g L = L_{g h g^-1} = L` by item 3. So `A_1` acts on `L` through a
   homomorphism `A_1 -> Aut(L)`. `Aut(L)` is infinite dihedral, hence solvable.
   A perfect group has only the trivial homomorphism to a solvable group, so the
   image is trivial. But `h` translates `L` by `l(h) > 0`, a contradiction.
5. Hence `tau_b = 0` for every `b in A_2`, so `A_2` fixes `L` pointwise. This
   contradicts the assumption that `A_2` fixes no vertex.

So `W` fixes a vertex. `∎`

**Referee notes.**
- *Where each hypothesis enters.* Finite generation is used only in (F2).
  Perfectness is used only in item 4. The swap is used in Step 1, both to make
  the `N`-orbit bounded and to transfer "no fixed vertex" from one factor to the
  other.
- *Calibration.* For `A = Z`, item 4 fails, since `Z` maps onto the translation
  subgroup, and `Z wr C_2` does act on a line without a fixed point. For
  `A = F_2` (not perfect), `F_2 wr C_2` maps onto `Z` by exponent sums, and the
  proof fails at the same item. Every other step is valid for arbitrary
  finitely generated `A`.
- *Previous panel.* Lenses 1 and 3 returned *survives*. Lens 2 lost its vote and
  raised no objection. This pass finds no gap.
