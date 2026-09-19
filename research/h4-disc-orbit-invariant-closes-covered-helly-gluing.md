---
rg: 2
id: h4-disc-orbit-invariant-closes-covered-helly-gluing
kind: claim
title: In H_4 the F-disc orbit has an integral H_1 invariant iota with saturated rank-60 image in Z^126, and the Z/2 Helly hull of three orbit discs passes this orbit test exactly when every pair of F-punctures lies in a common pair hull
distinct_from:
  h4-w15-coincidence-lifts-to-f45-x-flats-block-local-lifts: that bounds the H_1 rank of the disc orbit by 121 and asks (Q1); this computes the orbit lattice exactly, glues the three pair discs of a Helly triple through it, and decides (Q1) at the H_1 level pattern by pattern.
  h4-ker-rho-x-is-f45-mod-transported-collision-twists: that presents ker ρ_X; this uses its lifted model only to name the vertices of the Helly problem.
---

**Setting.** As in `h4-w15-coincidence-lifts-to-f45-x-flats-block-local-lifts`: `P° = F_45 ⋊ B°`, the fibre is
`ℂ` minus the 45 punctures `y_h`, and `μ̂ : P° → PB_46` tracks the punctures and the moving point `m`.
- `F_0, F_1, F_2` are the punctures of the walls `(1,0,0,0)`, `(1,1,0,0)`, `(1,1,1,0)`. The other 42 are *outside*.
- `Δ_F` is the base disc around `m, F_0, F_1, F_2`. The *orbit discs* are the discs `μ̂(g)Δ_F`, `g ∈ P°`.
  The y-vertices of the lifted model are orbit discs (w16, w17).
- x-vertices are arcs `t·x_0` from `m` to the base point `d_0`, with `t ∈ K = F_45 / R` realised by point-pushing `m`.
- `e_{pq}(σ)` is the exponent sum of the pure generator `A_{pq}` in `σ ∈ PB_46`. It is a homomorphism to `ℤ`.

**Theorem.**
1. **(The invariant.)** For a disc `D = σΔ_F`, `σ ∈ PB_46`, put `ι(D)_{a,j} = e_{F_a j}(σ) − e_{m j}(σ)` for
   `a ∈ {0,1,2}` and `j` outside. This gives `ι(D) ∈ ℤ^{126}`.
   - `ι(D)` depends only on `D`. Equivalently, `ι(D)_{a,j}` is the winding number of `j` around `σ(γ_a)·γ_a^{-1}`,
     where `γ_a` is an arc from `m` to `F_a` inside `Δ_F`.
   - Point-pushing `m` along a loop inside `D` does not change `ι(D)`.
2. **(The orbit lattice.)** The orbit discs adjacent to `x_0` are the discs `μ̂(s(β))Δ_F`, `β ∈ B°`, where `s` is
   the section. `ι` maps them into `Λ`, the ℤ-span of 122 vectors:
   - one vector for each of the 121 collision planes of `B°` (15 X-planes and 106 D-planes), namely the sum of `e_{pq}`
     over the pairs of punctures that collide on that plane;
   - and the vector `(−1, …, −1)`, which allows `m` to wind around all the punctures along a section loop.

   `Λ` has rank 60 in `ℤ^{126}` and is saturated. So orbit discs adjacent to `x_0` satisfy 66 independent integral
   linear equations.
   - 63 planes have a cluster through an F-puncture. Of these, 10 give vectors that mix different `F_a`.
   - In the 2-coordinate form `(e_{F_0 j} − e_{F_2 j}, e_{F_1 j} − e_{F_2 j}) ∈ ℤ^{84}`, which is invariant under all
     point-pushes of `m`, the image has rank 57 and is saturated.
   - Calibration: 60 random pure `A_{H_4}` words were pushed through the closed-form monodromy. Each gave a vector in
     the rational span of that 84-coordinate image.
3. **(Gluing.)** Take three x-vertices `x_0, x_2 = t_2x_0, x_3 = t_3x_0` and orbit discs `D_{12}, D_{13}, D_{23}`, where
   `D_{ik}` is adjacent to `x_i` and `x_k`.
   - Let `D` be the Z/2 Helly hull disc, and assume it contains `m, F_0, F_1, F_2`.
   - Let `S_E ⊂ {0,1,2}` be the set of F-indices in the pair hull `E` of `x_i, x_k`.

   Then for every `E` and every `a ∈ S_E`, `ι(D)_{a,·} = ι(D_{ik})_{a,·}`. So `ι(D)` lies in the *gluing closure*
   `Λ^{glue} = {z : π_{S_E}z ∈ π_{S_E}Λ for all three E}`.
4. **(H_1 form of (Q1).)** We enumerated the 38 patterns `(S_E)_E` with full hull F-set that are compatible with the
   homology of `t_2`, `t_3` and `t_2^{-1}t_3`.
   - `Λ^{glue} = Λ` holds exactly for the 23 *covered* patterns, those where every pair `{a, b}` lies in some `S_E`.
     In these the hull disc passes every abelian orbit test.
     - This includes the pattern `{01, 02, 12}`, where each pair hull holds two F-punctures.
     - It also includes every pattern with some `S_E = {0,1,2}`, where (Q1) holds trivially.
   - In the 15 uncovered patterns `Λ^{glue}` is strictly larger: rank 62 in 12 patterns and rank 67 in 3, against 60.
     - The extra directions are carried by the outside punctures of mixed-F planes. An example is
       `ζ = e^{(F_1−F_2)}_{r_{29}}` in the 84-coordinate form. Its three pair projections lie in the projected lattice,
       but `ζ ∉ Λ`.
5. **(The gap is not special to H_4.)** The same computation gives:
   - `A_4`: `Λ` has rank 3 in `ℤ^3`, and there is no gap.
   - `B_4`: `Λ` has rank 6 in `ℤ^{12}`, with gaps of 1 or 2.
   - `D_4`: `Λ` has rank 6 in `ℤ^9`, with gaps of 1 or 2.

   In `B_4` and `D_4`, exactly the same 15 uncovered patterns have gaps.

**Consequence.** At the level of `H_1`, (Q1) reduces to a statement about arcs in the plane.

*Pair covering:* in a Helly triple of orbit discs whose hull contains `F_a` and `F_b`, some pair hull contains both.

If pair covering holds, no abelian obstruction to (Q1) remains, and a counterexample to (H'') must be non-abelian.
If a triple realises an uncovered pattern, its hull disc is the candidate the brief asks for. Its `ι` can then be
tested against the 66 equations. The gaps in `B_4` and `D_4` show that an uncovered pattern is not a counterexample by
itself.

**Status.** proposed-established for items 1–5 (exact integer linear algebra; the identification of meridian images
and the gluing lemma are proved in the route). Open: pair covering, and non-abelian (Q1) in covered patterns.
