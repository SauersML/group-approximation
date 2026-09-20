---
rg: 2
id: thompson-f-two-transitive-cantor-case-orbit-counts
kind: claim
title: In the Cantor case of a 2-transitive action of Thompson's group F, the set is a product over every finite set of good cuts, the two-point stabilizer has exactly b, ab and a orbits on the three regions of a good orbit, and the point stabilizer has m^(n-1) orbits on increasing n-tuples
distinct_from:
  thompson-f-two-transitive-irrational-orbit-colorings: that claim splits the set as a product at one good point and proves the Cantor/interior dichotomy; this claim cuts at finitely many good points at once, proves that disagreement sets add over the cuts, and counts orbits of two-point stabilizers and of the point stabilizer on tuples of a good orbit
  thompson-f-two-transitive-actions-satisfy-grid-condition: that claim gives injectivity of the left/right orbit pair at one point; this claim uses the one-sided support criterion at irrational points and full products at good points
  thompson-f-two-transitive-disagreement-sets-are-not-cantor: that claim is the open half of the dichotomy; this claim splits it into two cases, m = 1 and m >= 2, each of which must be refuted separately, and records a Cantor set that passes every set-level test
  thompson-f-two-transitive-binary-colourings-force-regular-closed: that claim is about the interior case and does not touch the Cantor case; this claim is only about the Cantor case
---

Let `F` act on a set `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of distinct
points. Fix `ω ≠ ω'`. Put `H = F_ω` and `K = F_ω ∩ F_{ω'}`. Use `G_x`,
`D(·,·)` and `D_0` as in
`thompson-f-two-transitive-disagreement-sets-are-self-similar`, and good points,
`A_y`, `B_y`, `L_y = Ω/B_y`, `R_y = Ω/A_y` as in
`thompson-f-two-transitive-irrational-orbit-colorings`. For good irrational
`y < z` put `C_{y,z} = B_y ∩ A_z` (elements supported in some `[d,c]` with
`y < d < c < z`) and `M_{y,z} = Ω/(A_y B_z)`.

1. (One-sided support, every irrational `y`, both cases.)
   `ω_2 ∈ A_y ω_1` iff `D(ω_1,ω_2) ⊆ [0,y)`, and `ω_2 ∈ B_y ω_1` iff
   `D(ω_1,ω_2) ⊆ (y,1]`.
2. (Products over cuts.) Let `y_1 < … < y_n` be good irrational points. Then
   `ω_1 ↦ (B_{y_1}ω_1, A_{y_1}B_{y_2}ω_1, …, A_{y_{n-1}}B_{y_n}ω_1, A_{y_n}ω_1)`
   is a bijection
   `Ω → L_{y_1} × M_{y_1,y_2} × … × M_{y_{n-1},y_n} × R_{y_n}`.
   The stabilizer `F_{y_1} ∩ … ∩ F_{y_n}` equals
   `A_{y_1} × C_{y_1,y_2} × … × C_{y_{n-1},y_n} × B_{y_n}`, and it acts factor
   by factor. `A_{y_1}` is transitive on `L_{y_1}`, and `B_{y_n}` is transitive
   on `R_{y_n}`.
3. (Additivity.) In these coordinates `D(ω_1,ω_2)` is the disjoint union of
   pieces in `[0,y_1)`, `(y_1,y_2)`, …, `(y_n,1]`. Each piece depends only on
   the two corresponding coordinates, and it is empty iff they are equal.
4. (Two-point stabilizer.) Suppose `D_0` is a Cantor set (case (A)). Let `O` be
   a good irrational orbit and `y ∈ O`. Let `a` be the number of
   `(H ∩ A_y)`-orbits on `L_y \ {B_yω}`, and `b` the number of
   `(H ∩ B_y)`-orbits on `R_y \ {A_yω}`. Then `a, b ≥ 1`, and they do not
   depend on `y ∈ O`. Let `ξ < η` be the extreme points of `D(ω,ω')`. Then
   `O ∩ D(ω,ω') = ∅`, and `K` has exactly `b` orbits on `O ∩ (0,ξ)`, exactly
   `a` orbits on `O ∩ (η,1)`, and exactly `ab` orbits on `O ∩ (ξ,η)`. In
   particular `F` has exactly `(1+a)(1+b)` orbits on `Ω × Ω × O`.
5. (Tuples.) In case (A), for `O` as in item 4, let `m` be the number of
   `H`-orbits on increasing pairs in `O`. Then `F` is transitive on increasing
   `n`-tuples of `O`, and `H` has exactly `m^{n-1}` orbits on them. Moreover
   `m` is the number of `(H ∩ B_y)`-orbits on `O ∩ (y,1)` for any `y ∈ O`, and
   `m = 1` iff `G_y ∩ G_z` is transitive on `Ω` for some (equivalently every)
   `y < z` in `O`.
6. (Containments.) `K ⊇ H ∩ B_y` for every irrational `y > η`, and
   `K ⊇ H ∩ A_y` for every irrational `y < ξ`. In case (A),
   `K ⊇ H ∩ C_{y,z}` for all good irrational `y < z` in one gap of `D(ω,ω')`.
7. (Case split.) In case (A) exactly one of the following holds.
   - (A1) `m = 1`. Then `a = b = 1`, so `K` has exactly three orbits on `O`,
     namely `O ∩ (0,ξ)`, `O ∩ (η,1)` and `O \ [0,ξ] \ [η,1]`. In particular
     `K` is transitive on the gaps of `D(ω,ω')`, and `H` is transitive on
     increasing `n`-tuples of `O` for every `n`.
   - (A2) `m ≥ 2`. Then `H` is transitive on `O`, but it has at least
     `2^{n-1}` orbits on increasing `n`-tuples of `O`.
8. (Calibration.) Let `C` be the set of `x ∈ [0,1]` whose binary digits in odd
   places are `0`, and let `E = 1/2 + C/4`. Then `E` is a Cantor set in
   `(0,1)` with rational extreme points `1/2` and `7/12`. Every nonempty
   relatively clopen subset of `E` is `gE` for some `g ∈ F`. Some `s ∈ F` has
   `sE = E`, fixes both extreme points, and has germ slopes `4` at `1/2` and
   `1/4` at `7/12`. So `E` has every set-level property that items 2 and 4–7
   of the self-similar claim give `D_0`, together with items 1–3 of
   `thompson-f-two-transitive-hull-endpoints-are-rational` for the swap.

**What this changes.** Two things.

- Item 8 is a class kill. It kills every proof of
  `thompson-f-two-transitive-disagreement-sets-are-not-cantor` that uses only
  the shape of `D_0` together with the germ data of one element preserving it.
  Such a proof dies at the step where it concludes "not Cantor". Any proof
  must use the action on `Ω`, for example through the counts in items 4–5.
- Item 7 is the new decomposition. The not-Cantor claim is equivalent to
  refuting (A1) and (A2) separately.
  - (A1) is a subgroup `K` of `F` that is transitive on the gaps of a
    self-similar Cantor set and on the points of `O` in them, inside a point
    stabilizer that is order-transitive on `n`-tuples of `O` for every `n`.
  - (A2) is a transitive `H` whose orbit count on tuples of `O` grows
    exponentially.

Neither case is refuted here. See the Attempts section of the not-Cantor claim
for the exact step where the w14 attempt stopped.

Scope: proved here on 2026-09-19 by swarm agent `swarm-0917-w14-w14-z-break`.
The proof is elementary. It has no independent review, and no novelty is
claimed.

**Proof:** `thompson-f-two-transitive-cantor-case-orbit-counts-proof`.
