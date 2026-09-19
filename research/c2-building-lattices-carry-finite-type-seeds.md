---
rg: 2
id: c2-building-lattices-carry-finite-type-seeds
kind: claim
title: Every torsion-free type-preserving lattice in a thick locally finite C̃2 building carries a finite-type seed; the link-local method of the Ã2 node transfers, with generalized-quadrangle incidence at special vertices and complete bipartite residues at non-special ones
---

**ESTABLISHED** (lane proof, bh-invent-13, 2026-09-18; elementary building geometry; not reviewed). Items 1–2 are proved.
Rigidity of the seed is not addressed. `C̃_n` for `n ≥ 3` is OPEN (see the end).

## Setting

**Building and lattice.**
- `Δ` is a thick, locally finite building of type `C̃_2`, and `Γ ≤ Aut(Δ)` is a torsion-free, type-preserving, cocompact
  lattice. So `Γ` acts freely on the vertex set `V`, with finitely many orbits.
- Examples: torsion-free cocompact lattices in `Sp_4` over a nonarchimedean local field. They are Kazhdan (higher
  rank), Helly (CCGHO Thm 1.1(4)) and not hyperbolic.

**Vertices.**
- Vertices of types 0 and 2 are *corners*, and those of type 1 are *centers*.
- For a corner `x`, `Lk(x)` is a generalized quadrangle (GQ). Its points are the centers adjacent to `x` and its lines
  are the corners adjacent to `x`.
- For a center `c`, `Lk(c)` is a complete bipartite graph between its type-0 and type-2 corners, a generalized digon.

**Apartment model.**
- Corners are `Z²` (type 0 iff `a+b` is even), and centers are `(a+½, b+½)`.
- Chambers are the triangles {two adjacent corners, the center of their square}. The graph `G` is the whole 1-skeleton.
- Within an apartment, corner–corner distance is `ℓ¹` (every edge changes the coordinate sum by at most 1). For a
  center `c`, `d(c, o) = 1 + min_{k corner of c} ℓ¹(k − o)`.
- `d_Δ(v, o) = d_A(ρ(v), o)` for the retraction `ρ` onto an apartment `A` centred at a chamber containing `o`, because
  retractions are simplicial and are isometries on apartments through that chamber.

**Origins, labels, SFT.**
- Origins `o` range over one `Γ`-orbit `O = Γ·o_0` of type-0 corners.
- `y_o(x)` is `*` if `x = o`, and otherwise the *label* `λ_o(x)`, the inward set `In_o(x) = {y ~ x : d(y,o) < d(x,o)}`,
  encoded as below. Encoded in `Γ`-coordinates, these form a finite alphabet.
- `Y` is the set of configurations whose pattern on every star `St(x)` (with labels) equals that of some `y_o`, `o ∈ O`.

## Theorem

1. **(S1), (S2).** The only `η ∈ Y` with `η(o_0) = *` is `y_{o_0}`, and `Stab(y_{o_0}) = 1`.
2. **(S3).** `Y` is the orbit closure of `y_{o_0}`. So `(Y, *)` is an SFT compactification (a seed) of `Γ`, in the sense of
   `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`.

## Proof

**Step 0 (labels and local tables).** Take an apartment containing `o`, `x` and a neighbour `y`. Such an apartment
exists for any simplex and any vertex, and distances in it are building distances. Let `o − x = (a, b)`.

**(a) `x` a corner, `a, b ≠ 0`** (open quadrant). The label is the point `p` = the center of `x` towards `o`, and
`In = pencil(p)` = `p` together with all lines through `p`.
- Points: `p` gives −1, points collinear with `p` give 0, points not collinear with `p` give +1.
- Lines: lines through `p` give −1, all other lines give +1.
- *Check in the apartment (`a, b > 0`).* Points: `x+(½,½)` −1, `x+(−½,½)` and `x+(½,−½)` 0, `x+(−½,−½)` +1. Lines:
  `x+(1,0)` and `x+(0,1)` −1, `x+(−1,0)` and `x+(0,−1)` +1.
- *In the building.* Every apartment through `x` and `o` contains their convex hull, which contains `p`. GQ
  incidence (collinear, on a line through `p`) is intrinsic to `Lk(x)`, so each neighbour's apartment position is fixed.

**(b) `x` a corner, `b = 0 < a`** (wall). The label is the line `L = x+(1,0)`, and `In = {L}`.
- `L` gives −1, points on `L` give 0, and every other point and line gives +1.
- *Check.* `x+(½,±½)` gives `1 + (k−1)` with `k = a`, so 0. `x+(−½,±½)` gives +1. `x+(0,±1)` and `x+(−1,0)` give +1.

**(c) `x` a center.** The label is its *gate*, the unique nearest corner `g`, and `In = {g}`.
- The corners of the other type (all adjacent to `g`) give 0. The other corners of `g`'s type give +1.
- *Check.* Adjacent corners differ by exactly 1, since sides join types 0 and 2. Opposite corners cannot tie at the
  minimum: a tie at `(0,0)` and `(1,1)` forces `o_1 ≥ 1 ≥ o_2 + 1` or the reverse, and then `(1,0)` or `(0,1)` is strictly
  nearer.

So in every case the change `d(y,o) − d(x,o)` is a function of `λ_o(x)` and the incidence type of `y` in `Lk(x)`.
Changes are antisymmetric, so `y` is outward from `x` iff `x` is inward from `y`.

**Step 1 (outward determination).** For every outward `y`, `λ_o(y)` is a function of `λ_o(x)` and `y`. There is one
check per outward neighbour, in the apartment.
- **(a), `y` a line not through `p`.** `λ(y)` is the unique point of `y` collinear with `p` (the GQ axiom).
  - `y = x+(−1,0)`: `o − y = (a+1, b)`, so `λ(y) = x+(−½,½)`, which lies on `y` and on the line `x+(0,1)` through `p`.
  - `y = x+(0,−1)` is symmetric.
- **(a), `y` a point not collinear with `p`.** `λ(y) = x`: the corners of `x+(−½,−½)` are at `ℓ¹` distances
  `a+b, a+b+1, a+b+1, a+b+2`.
- **(b), `y` a line concurrent with `L`.** `λ(y) = L ∩ y`, the point: `o − (x+(0,1)) = (k,−1)`, so
  `λ = x+(½,½) = L ∩ y`.
- **(b), `y` a line not concurrent with `L`.** `λ(y) = x`, the line: `o − (x−(1,0)) = (k+1, 0)`.
- **(b), `y` a point not on `L`.** `λ(y) = x`: the corners of `x+(−½,±½)` are at `k, k+1, k+1, k+2`.
- **(c), `y` a corner of `g`'s type, `y ≠ g`.** `λ(y) = x`, the point.
  - Since `g` is the nearest corner, `o` lies in the closed quadrant beyond `g`.
  - So `o − y` has both coordinates `≥ 1`, and the center of `y` towards `o` is `x`.

**Step 2 (S1).** Suppose `η(o_0) = *`. The star of `o_0` is genuine only for `y_{o_0}`. Every vertex lies on a graph
geodesic from `o_0`, all of whose steps are outward. By induction with Step 1, `η = y_{o_0}`. `Γ` is free on `V`, so
`Stab(y_{o_0}) = 1`.

**Step 3 (descents).** Write `w → w'` if `w' ∈ In(w)`, as read from `η(w)`.
- **Diamond property.** Only case (a) has two or more inward neighbours, namely `pencil(p)`.
  - The star of `p` is genuine for some `y_{o''}`, which agrees with `η` on it.
  - In `y_{o''}`, `p` is inward from `x`. By (c), `x` is then a +1 corner of `p`, so `g'' := λ(p)` has `x`'s type.
  - The lines through `p` are sideways from `p`, so they have the other type. They are therefore adjacent to `g''`
    (complete bipartite) and lie at `d(p) = d(g'') + 1`.
  - Hence every element of `pencil(p)` has `→ g''`, and this is visible in `η` because it is read off the star of `p`.
    One-step diamonds make `→*` confluent.
- **Adjacent pairs have a common descendant.** Either one is inward from the other, or the pair is sideways. The
  sideways pairs are:
  - a point `q` collinear with `p` from (a): common descendant the line `pq`;
  - a point on `L` from (b): common descendant `L`;
  - a corner of the other type from (c): common descendant `g`.
  Each is read off the star of `w`.

**Step 4 (S3).** Let `η ∈ Y` contain no `*`, and fix `R`.
- As in `a2-lattices-carry-finite-type-seeds` Step 4, confluence gives one `z` below all of `B_R`, so `B_R ⊆ Out(z)`.
- By definition of `Y`, `η(z) = y_o(z)` for some `o ∈ O`.
- By Step 1 both `η` and `y_o` are determined on `Out(z)` by that label, so they agree on `B_R`.
- So `η` is a limit of translates of `y_{o_0}`. ∎

## What changed from Ã2, and `C̃_n`

**Changes from Ã2.**
- Labels are inward *sets*: a pencil or a line at corners, a corner at centers. The germ simplex of the CAT(0)
  geodesic no longer works, because in the ℓ¹-type 1-skeleton the inward set `{x+(1,0), x+(½,½), x+(0,1)}` is not a
  simplex of `Lk(x)`.
- The GQ axiom (a point off a line is collinear with exactly one of its points) replaces "two lines meet".
- Complete bipartite center residues supply the diamond.
- Origins are restricted to one `Γ`-orbit, which avoids the several-orbit caveat of
  `roller-compactifications-of-cube-complexes-are-sfts` part 4.

**`C̃_n` for `n ≥ 3` (OPEN).** Special links are polar spaces of rank `n`, and non-special links are joins of
projective and polar pieces. The natural replacement for the GQ axiom is the Buekenhout–Shult one-or-all axiom. The
case analysis of Steps 0–1 is not done.

## Lesson for general BH

- Finite-type seeds live on link incidence, not on the metric type. Once labels are taken to be inward sets rather than
  geodesic germs, the Ã2 proof runs on any building where:
  - (i) every outward label is fixed by one incidence axiom of the link (the "unique z");
  - (ii) the residues at non-special vertices provide one-step diamonds.
- For `C̃_2` these are the GQ axiom and complete bipartite digons. So Kazhdan, Helly, non-hyperbolic lattices (in
  `Sp_4(Q_p)`, say) have isolated dense seeds too.
- So (IE′) is expected wherever the link geometry has a unique-z axiom. It is proved for Ã2 and C̃2; C̃_n with `n ≥ 3`
  (polar spaces) and G̃2 (generalized hexagons) are the next cases. What remains there, as in Ã2, is rigidity.
