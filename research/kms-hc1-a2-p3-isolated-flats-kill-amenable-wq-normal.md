---
rg: 2
id: kms-hc1-a2-p3-isolated-flats-kill-amenable-wq-normal
kind: claim
title: "The A~2 root-word quotient Gamma_3 has isolated flats: it is hyperbolic relative to virtually Z^2 flat stabilizers and contains Z^2 = <bcba, babc>, so no infinite amenable subgroup is wq-normal and no commuting chain of infinite-order elements generates it"
distinct_from:
  fpbs-hyperbolic-no-q-normal-hyperfinite-chain: that claim is about free actions of hyperbolic groups and q-normal chains of subrelations. Gamma_3 is not hyperbolic; this claim proves it is relatively hyperbolic, and uses that only for subgroup chains.
  fpbs-amenable-wq-normal-relative-subcriticality: that claim uses an amenable wq-normal subgroup as an input for percolation. This claim shows Gamma_3 has no such subgroup.
artifacts:
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/link_geodesics.py
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/link_geodesics.out
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/flat_rank.g
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/flat_rank.out
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/flat_certs.py
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/flat_certs.out
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/tube.py
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/qball.py
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/q5j3.txt
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/export_pc.g
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/qsearch.py
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/wqclosure.py
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/wqclosure.out
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/sdp_sym.py
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/wedderburn.py
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/groupball.py
  - experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19/sos_runs.out
---

## Setting

`Gamma_3 = Gamma^A2_3` is the group of `kms-hc1-root-word-infinite-in-a2-quotient` at `p=3`:

```text
Gamma_3 = < a,b,c | a^3, b^3, c^3, [a,b,a], [a,b,b], [b,c,b], [b,c,c], [a,c,a], [a,c,c] >.
```

It is the fundamental group of a triangle of groups. The vertex groups
`U_ab`, `U_bc`, `U_ca` are Heisenberg of order 27. The edge groups are
`<a>`, `<b>`, `<c>`, and the face group is trivial. Give each triangle the
Euclidean equilateral metric. `X_3` is the development: triangles are the
elements of `Gamma_3`, and `Gamma_3` acts simply transitively on them.

## Statement

**ESTABLISHED** (literature theorems plus exact finite computations).

1. **Links.** Every vertex link `L` of `X_3` is a cubic bipartite graph on
   18 vertices. It has girth 6 and diameter 4. It is distance-regular with
   intersection array `{3,2,2,1; 1,1,2,3}` (the Pappus graph). Any two
   vertices of `L` at distance 3 are joined by **exactly two** geodesics.
   So `X_3` is CAT(0), and the vertex groups embed. This is checked in
   `link_geodesics.py` / `.out`.
2. **No flat triplanes.** `X_3` contains no isometrically embedded flat
   triplane. A flat triplane is three Euclidean half-planes glued along
   their boundary line.
3. **Isolated flats and relative hyperbolicity.**
   - By Hruska's triplane criterion (Geom. Topol. 8 (2004)), `X_3` has
     isolated flats.
   - By Hruska--Kleiner (Geom. Topol. 9 (2005), Thm 1.2.1), `Gamma_3` is
     hyperbolic relative to the family `P` of its maximal virtually abelian
     subgroups of rank 2. These are the flat stabilizers; each is virtually
     `Z^2` and acts cocompactly on its flat.
   - `Gamma_3` is not virtually abelian, since it contains `<r,s> = C_3*C_3`.
     So this structure is non-elementary, and `Gamma_3` is acylindrically
     hyperbolic.
4. **An explicit flat.** Put `u = bcba` and `v = babc`. Then:
   - `[u,v] = 1` in `Gamma_3`, proved by an exact tube certificate;
   - `u`, `v` and `vu^-1` have infinite order;
   - `<u,v>` is virtually `Z^2`. Its image in `Gamma_3/P_7` (order `3^22`)
     has abelian invariants `[9,9]`, while every quotient of `Z x F` with
     `F <= (Z/3)^2` has cyclic `3`-multiple.

   So `Gamma_3` is **not hyperbolic**, and `P` is non-empty. Also
   `(ba)^-1 u (ba) = AcAB` holds with `AcAB` in `C(u)` (`flat_certs.out`).
5. **Obstruction (class-killing).** Let `A <= Gamma_3` be an infinite amenable
   subgroup. Then `A` lies in a unique maximal elementary subgroup `E(A)`.
   Either `E(A)` is a conjugate of a flat stabilizer (virtually `Z^2`), or
   it is `E(h)` for a loxodromic `h` (virtually `Z`). `E(A)` is almost
   malnormal, so every weakly quasi-normal chain starting at `A` stays inside
   `E(A)`, which is a proper subgroup. Hence:
   - (a) `Gamma_3` has **no infinite amenable wq-normal (or q-normal, or
     s-normal) subgroup**. So Peterson--Thom's criterion (Invent. Math. 185
     (2011), Thm 5.12) and Popa's wq-normal rigidity cannot give
     `b_1^(2)(Gamma_3) = 0` from any amenable start.
   - (b) Take infinite-order elements `g_1, ..., g_n` with
     `[g_i, g_{i+1}] = 1`. They all lie in one `E(g_1)`, so they never
     generate `Gamma_3`. Gaboriau's commuting-chain criterion for
     `b_1^(2) = 0` and for fixed price 1 therefore does not apply.

   This matches the computation. Starting from `bcba` (and earlier from
   `t_a = [a,b][c,a]`), the exact wq-closure stalls inside the ball of
   radius 7, at `|H cap B_7| = 37` (`wqclosure.out`).
6. **What survives, and the reduction it gives.**
   - Relative hyperbolicity does not decide `b_1^(2)`. Property (T) is also
     not excluded: the symmetry-reduced Ozawa SDP gives only numerically zero
     `lambda` at radii 2, 3 and 4 (`sos_runs.out`).
   - Suppose `Gamma_3` acts properly and cocompactly on a CAT(0) cube
     complex. Then it is virtually compact special (Oregón-Reyes, Groves--
     Manning, for virtually abelian peripherals). Virtually compact special
     groups satisfy the strong Atiyah conjecture (Schreve, Math. Ann. 2014),
     with denominators dividing 27 here.
   - The unconditional bound `b_1^(2)(Gamma_3) <= 0.006258 < 1/27` (lane w26,
     `kms-hc1-a2-p3-first-l2-betti-below-atiyah-threshold`) would then give
     `b_1^(2)(Gamma_3) = 0`.
   - So **cubulating `Gamma_3` suffices**. Any cubulation must also rule out
     (T) (Niblo--Reeves), so it cannot come from the Ozawa side.

Proof: `kms-hc1-a2-p3-isolated-flats-kill-amenable-wq-normal-proof`.

## Attempts

1. **Commuting / wq-normal closure from an infinite element (w27-057).**
   This is dead by part 5. Exact closures in the certified ball stall at 6
   nodes from `t_a` and at 12 nodes from `bcba`. The wq-closure of `<bcba>`
   stalls at `|H cap B_7| = 37`. Part 5 explains why.
