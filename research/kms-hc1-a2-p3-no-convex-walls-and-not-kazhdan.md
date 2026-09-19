---
rg: 2
id: kms-hc1-a2-p3-no-convex-walls-and-not-kazhdan
kind: claim
title: "Gamma_3 is not Kazhdan (its index-3^6 p-central term P_3 is torsion-free with abelianization Z^24 + Z/3), but its CAT(0) triangle complex X_3 has no convex wall at all; so the kernel of the pro-3 completion onto the Iwahori is infinite, and any cubulation needs non-convex quasiconvex walls"
distinct_from:
  kms-hc1-a2-p3-isolated-flats-kill-amenable-wq-normal: that claim proves isolated flats and relative hyperbolicity, and kills the amenable wq-normal and commuting-chain routes; it leaves (T) open. This claim refutes (T) and rules out convex walls in X_3.
  lifted-thompson-t-convex-line-walls-are-trivial: that is about convex line walls for a Thompson-type group acting on a line; this is about convex tracks in a CAT(0) 2-complex with Pappus links.
artifacts:
  - experiments/kms-hc1-a2-p3-median-walls-2026-09-19/not_t.g
  - experiments/kms-hc1-a2-p3-median-walls-2026-09-19/not_t.out
  - experiments/kms-hc1-a2-p3-median-walls-2026-09-19/pappus_cuts.py
  - experiments/kms-hc1-a2-p3-median-walls-2026-09-19/pappus_cuts.out
---

## Setting

`Gamma_3`, `X_3`, the Pappus link `L` and the vertex groups `U_ab`, `U_bc`,
`U_ca` are as in `kms-hc1-a2-p3-isolated-flats-kill-amenable-wq-normal`:

```text
Gamma_3 = < a,b,c | a^3, b^3, c^3, [a,b,a], [a,b,b], [b,c,b], [b,c,c], [a,c,a], [a,c,c] >.
```

`X_3` is the CAT(0) development with equilateral triangles.
`P_k = P_k(Gamma_3)` is the lower exponent-3 central series, and
`phi^: Gamma_3^ -> I_1` is the surjection of pro-3 groups from
`kms-hc1-a2-pro-p-completion-is-iwahori-criterion`.

A **convex wall** in `X_3` is a closed convex subset `W` with empty interior
such that:

- `X_3 \ W` has exactly two components `H+` and `H-`;
- every point of `W` lies in the closure of both.

`W` need not be invariant under any subgroup.

## Statement

**ESTABLISHED.** The proofs use exact finite computations (GAP, and an
exhaustive enumeration) together with standard theorems.

1. **Virtual first Betti number 24.**
   - `P_3` is a normal subgroup of index `3^6` and is torsion-free.
   - `P_3^ab = Z^24 + Z/3`.
   - `P_2` has index 27 and `P_2^ab = (Z/3)^5`.
   - `Y = X_3/P_3` is a compact non-positively curved 2-complex. It has 81
     vertices, 729 edges and 729 triangles, so `chi(Y) = 81 = 3^6 chi(Gamma_3)`.
   - Its Betti numbers are `b_1(Y) = 24` and `b_2(Y) = 104`.
2. **Not (T).** `Gamma_3` does not have property (T), since a finite-index
   subgroup has infinite abelianization.
   - By Ozawa's theorem, no sum-of-squares certificate
     `Delta^2 - lambda Delta = sum xi_i^* xi_i` with `lambda > 0` exists at
     any radius. This explains the numerical `lambda ~ 0` of w27.
   - The "prove (T)" alternative of the cubulation question is refuted.
   - `Gamma_3` still maps onto the Kazhdan group `U_+ = SL_3(F_3[t]) cap I_1`.
3. **No convex walls.** `X_3` contains no convex wall.
   - Inside triangles, a convex wall runs along altitudes. It crosses edges
     perpendicularly in all three sheets, or else runs along edges.
   - At a vertex it therefore gives a set `S` in the Pappus link. `S` consists
     of link vertices and link-edge midpoints at pairwise distance `>= pi`,
     and the sides must admit a 2-colouring.
   - Exhaustive enumeration finds no admissible `S`:
     - of the 1293 far-apart sets, 0 admit a valid colouring;
     - in particular, of the `2^17` bipartitions, 0 have an induced-matching
       edge cut (`pappus_cuts.out`).
   - More precisely, every locally two-sided track through a vertex has two
     median directions at angle `<= 2pi/3`. 45 of the 10125 two-sided local
     shapes reach `2pi/3`, and the other 10080 have angle `pi/3`.
4. **Consequence for the target.** `ker phi^` is **infinite**. It lies in
   the closure `bar P_3`, and it surjects onto a finite-index subgroup of
   `bar P_3^ab = Z_3^24 + Z/3`.
   - The reason is structural. Every open subgroup of `I_1` has finite
     abelianization, because `sl_3(F_3)` is perfect. But the pro-3
     completion has the open subgroup `bar P_3`, whose abelianization is
     infinite.
   - This upgrades (T3) of the target, which found `ker phi^` nontrivial
     from a tower deviation at class 6.
5. **What is left for cubulation.**
   - Sageev and Niblo--Reeves do not forbid cubulation: `P_3` has
     codimension-1 subgroups, namely the kernels of the maps `P_3 -> Z`.
   - Walls taken as convex subsets of `X_3` cannot exist (part 3). So a
     proper cocompact cubulation, for example via the Hruska--Wise relative
     criterion, needs one of:
     - relatively quasiconvex codimension-1 subgroups whose tracks in `X_3`
       genuinely bend;
     - a different CAT(0) model.
   - The reduction of w27 (cubulation implies `b_1^(2)(Gamma_3) = 0`) is
     unchanged.

Proof: `kms-hc1-a2-p3-no-convex-walls-and-not-kazhdan-proof`.

## Attempts

1. **Convex median walls (w28-057).** Dead by part 3.
2. **Ozawa certificate for (T) (w27-057, w28-057).** Dead by part 2.
