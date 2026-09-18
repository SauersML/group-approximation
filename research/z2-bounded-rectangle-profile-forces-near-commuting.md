---
rg: 2
id: z2-bounded-rectangle-profile-forces-near-commuting
kind: claim
root: true
title: Unitary pairs whose rectangle commutators satisfy rank([b^s,c^t]-I) <= K(s+t) for all s,t are within rank F(K) of a commuting pair
distinct_from:
  z2-commuting-pairs-are-not-bounded-rank-stable: that refutes stability under a bounded commutator rank; this assumes a bounded linear profile over all rectangle words, which both the dislocation dipole and the slit origami violate.
  slit-origami-z2-pair-has-rank-distance-half-l: that computes the rank distance of one pair with quadratic profile; this asks whether a linear profile forces bounded distance.
  near-exact-tuples-saturate-linear-conversion-defect: that proves the converse direction (distance delta gives profile constant 2 delta) and that linear order is the near-exact noise floor; this is the forward direction.
  deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension: that is the rung; this is the commuting-rounding input its long-root route needs for g >= 5, not the rung itself.
---

**OPEN.**

**Statement.** Define the rectangle profile of unitaries `b, c` in `U(d)` as
`Lambda_rect(b,c) = sup_(s,t >= 1) rank([b^s, c^t] - I) / (s + t)`. There is a function `F` such that
`Lambda_rect(b,c) <= K` implies that some commuting pair `b', c'` (after padding by `U(m)`) has
`max(rank(b' - b (+) beta), rank(c' - c (+) gamma)) <= F(K)`. The bound must not depend on `d`.

**Converse (proved).** Rank distance `delta` gives `Lambda_rect <= 2 delta`: this is Lemma B of
`near-exact-tuples-saturate-linear-conversion-defect-proof`. So, if the statement holds, the rectangle
profile is a coarse (bounded-rank-invariant) measure of the distance to commuting pairs.

**Why this is the right target.**
- Every word-growth invariant has its near-exact noise floor at linear order
  (`near-exact-tuples-saturate-linear-conversion-defect`). So sublinear forms such as "conversion
  defect `o(L)`" are false, and linear order is the finest scale at which an invariant of this kind can see.
- `sln-relators-force-linear-commutator-growth` gives `Lambda_rect(rho(u), rho(v)) <= C_n k` for
  every commuting root pair of a rank-`k` tuple of `SL_n(Z)`, `n >= 5`. The extension to `s != t` is the
  same proof: `Area([u^s, v^t]) <= C_2 (s + t) + O(log^4 (s + t))` via `W_s(u)`, `W_t(v)`. This covers
  Deligne sector tuples with `g >= 5` through the `SL_g(Z)` Levi.
- Both known far-from-commuting families with bounded commutator rank have quadratic profile up to
  their defect scale: the dislocation dipole and the slit origami, `phi(m) = 2 m^2`. No pair is known
  that has bounded `Lambda_rect` and is far from commuting.

**Reduction (one direction).** Suppose the statement holds. Then for `g >= 5` the commuting root pair
`(rho(e_13), rho(e_23))` of the `SL_g(Z)` Levi of every rank-`k` sector tuple lies within rank `F(C_g k)` of a commuting
pair. This is the rounding input that the joint-spectrum route of the rung needed and that
`z2-commuting-pairs-are-not-bounded-rank-stable` showed cannot come from `Z^2` alone. It does **not**
by itself give the rung. The atom-level `SL_2(Z)` rigidity step recorded in the rung's Attempts
(interlacing) is still needed after rounding.

**Easiest nontrivial case and first falsifiable step.** Take permutation pairs, that is, square-tiled
surfaces. Here `rank([b,c] - I)` bounds the total cone excess. A rectangle loop based at `x` fails to
close only if the rectangle at `x` meets the singular set with nontrivial monodromy. `Lambda_rect <= K`
forces every cone point to have flat injectivity radius `O(K)`, because an embedded `R x R` cone disk
gives `~R^2/4` non-closing loops at scale `R/2`. The step to check is whether each cone point then
lies on a saddle connection or cylinder boundary of length `O(K)` whose regluing removes it at rank
cost `O(K)`, so that `F(K) = O(K^2)` for permutations. The examples fit this picture:
- slit of length `s`: `Lambda ~ s`, distance `s/2`;
- L-shaped origamis: distance `<= 2`;
- tall thin cylinders of circumference `c_0`: `Lambda ~ c_0`, regluing cost `c_0`.

A counterexample would need cone points whose short loops are all diagonal, or a genuinely
non-permutation unitary construction.

## Attempts

- **Cone-radius regluing for permutation pairs (2026-09-18, w6-124, transplanter). Where it stops.**
  - **Proved.** An embedded flat `R x R` disk around a cone point gives about `R^2/4` non-closing
    rectangle loops at scale `R/2`. So `Lambda_rect <= K` bounds every flat injectivity radius by
    `O(K)`.
  - **Where it stops.** A short injectivity radius yields a short closed curve through the cone point,
    but not one along the `b` or `c` direction. The regluing step needs a horizontal or vertical saddle
    connection of length `O(K)`. If every short connection is diagonal, cutting along it changes the
    rank of both `b - b'` and `c - c'` by its combinatorial length in the other generator. No bound in
    `K` for that length is known yet.
  - **General unitaries.** Beyond permutations there is no singular set. The profile controls
    `rank([b^s,c^t] - I)` only, which gives interlacing and not atoms: the same barrier as the rung's
    D2 attempt. The permutation case is the first step to settle.
- **GL2(Z) change of generators plus band surgery (2026-09-18, w7-124, transplanter). Settles the abelian
  class; the non-abelian thin case is open.**
  - **Proved** (`torus-abelian-covers-rectangle-profile-near-commute`). Take any regular abelian cover
    of a square-tiled torus, with any number of squares. Rectangle profile `K` gives distance
    `exp(O(K log K))`. For dipole covers (for example the slit origami) the bound is `3072 K^4`.
  - **How the diagonal gap closes.**
    - Rewrite the pair in the basis `(v, u)`, where `v` is the primitive shortest lattice direction:
      `B = b^(v1) c^(v2)` and `C = b^(u1) c^(u2)`.
    - The short diagonal becomes the generator `B`. Cut and reglue `C` along the rows of `B`
      (the band surgery).
    - Back-substitute `b'' = B^(u2) C''^(-v2)` and `c'' = B^(-u1) C''^(v1)`. The cost is
      `6 |A| n lambda_1^4`, where the charge count `|A| n <= 4K` comes from Stokes.
    - When `lambda_1` is large, hierarchical clustering of the charges shows that the profile forbids
      non-neutral clusters.
  - **Computation.**
    - Exhaustive for Z/2 dipole covers with `N <= 40` (exact profile).
    - For `N <= 22`, the explicit commuting pairs are within `2.5 K` in every case.
    - General loops beat rectangles by at most `1.25x`.
    - Result: no counterexample. In range, the distance is linear.
  - **Where it stops.** General origamis are covers with non-abelian fibre. In the thin case, the row
    monodromies of `B^k` at the two ends of a band are conjugate rather than equal. Regluing needs a
    conjugating fibre bijection, whose rank cost is not yet bounded by `K`. Bounding that cost is
    the next step.
- **Conjugating fibre bijections for the non-abelian thin case (2026-09-18, w8-124, transplanter).
  Dead: the step is false.**
  - **Proved** (`centralizer-rounding-cannot-bound-rank-distance-by-profile`). The example is a
    cross-slit pair on `(Z/p)^2 x Z/2`, with one swap on `b` and one swap on `c`. It has profile at most
    2 and distance 1. Yet every commuting pair that keeps a word `b^v1 c^v2` with `|v|_1 < p`, and
    changes only the other generator inside its centralizer, costs at least `2p`.
  - **Why this settles the step.** Over the one-square torus every permutation pair is thin, and
    band surgery there means "keep `b`, conjugate `c`". So the conjugator cost of the proposed step is
    not bounded by any function of `K`.
  - **Why it fails.** The 2p-cycles of the kept word lie over a proper set of base orbits. The other
    generator translates that set, so every conjugator must move it.
  - **Computation** (exact: all frames for `p = 11, 13, 17`, and cylinder variants). On random
    `S_3`, `Q_8` and `A_4` slit covers, one-sided rounding stays within `3.4 K`. Those covers have long
    slits, whereas the obstruction lives in short cross slits.
  - **What it leaves.** Any proof of the forward statement has to be two-sided and local near the
    defects: it must change both generators, as the abelian path cuts do. For general permutation
    pairs, the open step is a local two-sided surgery around non-commuting cone points whose cost
    is bounded by the profile.
- **w8-124, 2026-09-18 — two-sided strip cut for abelian dipoles. Landed: F(K) <= 24 K on dipole covers.**
  See `torus-dipole-covers-rank-distance-linear-in-profile`.
  - **Method.** Cut the row circle of the shortest lattice direction at the two charged rows, and reglue each
    arc into its own torus. This redirects `2 lambda_1` moves. Then cancel the seam charges along a
    digital line of `lambda_1` squares. In total `6 lambda_1` sites change, so `dist <= 6|A| lambda_1 <= 24 K`.
  - **Result.** This replaces the `3072 K^4` of the dipole case. It is linear, as the data had
    suggested.
  - **Computation.** Checked assertion by assertion on 4342 exhaustive cases (`N <= 20`). The construction
    has `dist/K <= 4.5`, and the best of all two-cuts has `dist/K <= 1.67` (`N <= 16`).
  - **Open.** Two steps remain:
    - several charges, where the merged clusters are not neutral; a cost of `O(|A|(n lambda_1 + n^2))` looks
      plausible for the thin case;
    - non-abelian fibres, where band cancellation needs the ordered product of the charges to be trivial.
