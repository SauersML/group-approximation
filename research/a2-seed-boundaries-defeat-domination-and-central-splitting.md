---
rg: 2
id: a2-seed-boundaries-defeat-domination-and-central-splitting
kind: claim
title: A midpoint-covering lemma turns domination into far commutation, and it proves the tree case; in Ã2 seed boundaries chamber-field patterns block every midpoint covering, and the wall strata are open but not closed, so neither tree-type forcing nor central splitting proves the Ã2 seed rigid
requires:
  - a2-seed-rigidity-reduces-to-its-perfect-boundary
distinct_from:
  free-group-boundary-shift-is-quantum-rigid: that proves rigidity by domination chains; the covering lemma here is a reformulation that makes explicit what those chains need, namely that every midpoint letter dominates an end, which Ã2 boundaries violate.
  quantum-rigidity-is-decided-on-the-derived-subshift: that splits off central idempotents of locally forced isolated points; this shows the wall strata admit no finite-pattern splitting from the chamber stratum, since their union is open but not closed.
  rigid-subshifts-over-free-factors-are-tight-almost-everywhere: that derives structure from rigidity over free factors; it is not a source of rigidity, and Kazhdan Ã2 lattices have no free factor.
  a2-lattice-phase-seeds-are-quantum-rigid: that is the open claim; this closes the tree-type and splitting strategies for it.
---

**ESTABLISHED** (lane proof, bh-emitter-b, 2026-09-18; elementary; not reviewed).

**Notation.** `Y` is a subshift over `Γ`. For each label `a` at a site `x`, let `Out(x, a)` be a set
of sites that `a` **dominates**: in every `D`-quantum family, `E_a(x) ≤ E_(f(u))(u)` for each
`u ∈ Out(x, a)`, for a forced label `f(u)`. For the Ã2 seeds (`a2-lattices-carry-finite-type-seeds`,
Step 5), `Out(x, a)` is the outward-reachable set.

## Statement

1. **Covering lemma (any `Y`).** Suppose that every pair of sites at distance `< d` has commuting
   letters, and let `d(q, q') = d`. Suppose also that there is a finite `M` with the following
   properties:
   - `d(m, q) < d` and `d(m, q') < d` for all `m ∈ M`;
   - `M` lies in a ball of radius `D`;
   - every pattern on `M` that occurs in `Y` has a site whose letter dominates `q` or `q'`.

   Then the letters at `q` and at `q'` commute. For trees, `M = {m}` works for any interior vertex
   `m` of `[q', q]`: every pointer at `m` points away from `q` or from `q'`, and `*` dominates both.
   This recovers rigidity of the end shift of `F_n`.
2. **Midpoint coverings fail in Ã2 boundaries.** Let `Y = ∂Y_Γ` or `∂Y_Γ^(N)`, and fix `R`. There are
   pairs `q, q'` at arbitrarily large distance, with midpoint `m`, such that some pattern of `Y` on
   `B_R(m)` (that of a chamber field `x_c`) has no site dominating `q` or `q'`.
3. **The wall strata are open but not closed.** `U = {η ∈ ∂Y : η has a wall label}` is open and
   invariant, and every point of the chamber stratum is a limit of points of `U`. So no idempotent
   built from finitely many letters separates the strata.

## Proof

1. **Covering lemma.** Write `E_a = E_a(q')`, `E_b = E_b(q)` and `E_c = E_c(M)` for the product over
   a pattern `c` on `M`. The `E_c` over occurring `c` sum to `I`. They come from expanding the commuting
   partitions of unity on `M`, and a non-occurring `c` vanishes by (Q3), after expanding to the
   `D`-ball that contains `M`. By hypothesis each `E_c`
   commutes with `E_a` and with `E_b`.
   - If `c` has a site dominating `q'`, then `E_c E_a = δ E_c` with `δ ∈ {0, 1}`. So
     `E_c E_a E_b = δ E_c E_b`, and `E_c E_b E_a = E_b E_c E_a = δ E_b E_c = δ E_c E_b`.
   - The case of a site dominating `q` is symmetric.
   - Summing over `c`: `E_a E_b = Σ_c E_c E_a E_b = Σ_c E_c E_b E_a = E_b E_a`.
   - For trees, take `M = {m}`. A pointer at `m` toward `q` leaves `q'` in its outward region, and
     conversely; any other pointer dominates both.
   - Induction on `d` from the base case `d <= 2D` (Q2) gives rigidity. `∎`
2. **Failure in Ã2 boundaries.**
   - **Setup.** Fix an apartment `A`, a chamber `c ∈ Ω` of `A`, and the retraction `ρ` onto `A`
     centred at `c`. It preserves the Busemann height `b` of `x_c` (the limit of `d(o_k, ·)`
     differences) and does not increase distances.
   - **Outward sites lie in a cone.** Outward steps raise `b` by 1, and `b` is 1-Lipschitz. So
     `z ∈ Out(x)` forces `b(z) − b(x) = d(x, z)`. Applying `ρ` gives
     `b(ρz) − b(ρx) = d(ρx, ρz)` inside `A`. On `A` the hexagonal Busemann function is linear, and
     equality holds iff `ρz − ρx ∈ K̄`, the closed 60° cone of outward directions of `x_c`.
   - **The pair.** Take `q, q' ∈ A` on a line through `m` whose direction lies outside `K̄ ∪ −K̄`.
   - **Conclusion.** For `x ∈ B_R(m)`, the point `ρx` lies within `R` of `m`. Once
     `d(m, q), d(m, q') ≫ R`, the vectors `q − ρx` and `q' − ρx` lie outside `K̄`. So no site of
     `B_R(m)` dominates `q` or `q'` in `x_c`, and `x_c ∈ ∂Y` (`a2-lattices-carry-finite-type-seeds`, Step 6).
3. **Openness and closure.**
   - `U` is a union of cylinders.
   - For a chamber-stratum `η` and `R`, Step 4 of `a2-lattices-carry-finite-type-seeds` gives `z` with
     `B_R(1) ⊆ Out(z)` and `η(z)` a flag.
   - The limits of `y_(o_k)` with `o_k = z − kω_1 − jω_2` (`j >= 1` fixed, residues fixed for phases)
     agree with `η` on `B_R(1)`, and they have a wall label at `z − jω_2`.
   - In any commutative representation, an idempotent built from finitely many letters is the
     indicator of a clopen set, and no clopen invariant set separates `U` from its closure. `∎`

**Remark (thickness).** Double domination does occur in Ã2 boundaries. A flag `(p_0, ℓ_0)` at `m`
dominates both ends of a geodesic whose germs at `m` are a point off `ℓ_0` and a line not through
`p_0` that are antipodal. So item 2 is not a counting obstruction. It fails because the chamber
fields point sideways.

## What this closes, and what is left

- **Tree-type forcing.** The wall sets carry the free-group pointer structure, and item 1 would turn
  that into rigidity if coverings existed. Item 2 shows that the chamber stratum, which lies in the
  closure of every wall stratum, blocks the midpoint coverings `M = B_R(m)` at every radius.
  - So the covering scheme with midpoint balls cannot prove `∂Y` rigid. Coverings by other sets `M`
    in the lens between `q` and `q'` are not ruled out here (not checked).
  - This matches the fact that `X_Ω` and `P` have rigidity proofs only through finite presentation.
- **Central splitting.** Item 3 shows that the wall strata do not split off from the chamber stratum
  by central idempotents of finite patterns. A relative derived-subshift theorem would need a
  mechanism for non-clopen seams.
- **What survives.**
  - A finitely presented host for `G_V × (Γ ⋉ ∂Y^(N))`, certifying the whole perfect boundary at
    once, as the host of `a2-lattice-boundary-skew-shifts-are-quantum-rigid` does for `P`.
  - Or cylinder transport over a rigid factor (`a2-busemann-transplants-preserve-quantum-rigidity`).
    But `∂Y` has no equivariant factor onto the chamber stratum: a wall configuration determines no
    chamber.

## Lesson for general BH

The rank-one proof of rigidity is a covering argument. Every midpoint letter must dominate one end, so
far commutation follows by induction on distance. In rank two the outward cones are narrower than
half-spaces, and sideways chamber fields defeat the midpoint coverings at every radius. So
higher-rank rigidity is unlikely to be assembled from local forcing. The proved route certifies it
globally, by finite presentation of a host. For seeds on Kazhdan lattices this makes the host for the whole boundary, a non-minimal
groupoid with an open orbit, the one remaining object of rung 1d.
