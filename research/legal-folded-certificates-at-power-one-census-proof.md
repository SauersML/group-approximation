---
rg: 2
id: legal-folded-certificates-at-power-one-census-proof
kind: route
title: Project a legal f-folded fatgraph to dart types and vertex polygons; exact Farkas vectors kill 6372 automorphisms, and the 48 LP-negative ones have verified certificates
target: legal-folded-certificates-at-power-one-census
requires:
  - legal-f-folded-fatgraphs-give-surface-subgroups
  - positive-f-folded-fatgraphs-have-only-even-valence
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp_allwords.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_allwords.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_allwords_m1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/classes.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_batch.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m1_census.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/validate_certificates.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/validate_certificates_m1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
---

Notation: `phi` is a positive automorphism from `phi_scan4.json`, `f` its rose map, and `M` its
matrix. Upper case is inverse. `R(x) = f(x)^-1` is the *block* of the direction `x`. `g` is the
gate map: the `Df`-periodic direction reached after `4 * 6 + 4` steps. Two directions share a
gate iff some iterate of `Df` agrees on them, iff these periodic images agree.

**Step 1: what a certificate looks like.** Let `X` be a legal `f`-folded fatgraph.

- Its boundary is `partial^- ⊔ partial^+`. For each `partial^-` word `w = x_1 ... x_L`, there is a
  `partial^+` circle reading `R(x_L) ... R(x_1)`. The `f`-corners are the block junctions.
- Every turn `(x, y)` of a `partial^-` word is legal, `g(X^-1) != g(y)`, by (L) at its corner.
  Legal turns do not cancel under `f` (Step 8 of `positive-f-folded-fatgraphs-have-only-even-valence-proof`),
  so each `partial^+` circle is a reduced cyclic word.
- `partial^-` is non-empty, since `X` has at least one edge and so at least one boundary circle,
  and `partial^+` circles come with `partial^-` circles.
- `[partial^-] + [partial^+] = 0` in `H_1(F)`, since the boundary of the surface of `X` is
  null-homologous in `X`. With `[partial^+] = -M [partial^-]` this gives `(I - M)[partial^-] = 0`.
  `chi_M` is an irreducible cubic, so `det(I - M) = -chi_M(1) != 0`. Hence `[partial^-] = 0`.

**Step 2: dart types.** Every dart of `X` (oriented edge on a boundary circle) gets a type:

- `('-', x, y)`: a `partial^-` dart with label `x`, followed on its circle by label `y`;
- `('+', x, i)` for `0 <= i <= |R(x)| - 2`: letter `i` of a block `R(x)`;
- `('L', p, x)`: the last letter of a block `R(x)` whose circle continues with the block `R(p)`.
  Then `p x` is a turn of the `partial^-` word.

The type determines the label, whether the dart is a `partial^-` dart, and whether it is an
`f`-dart (the first letter of a block). The type of the next dart on the circle is a *successor*
of the type of the dart. Let `c_xy` be the number of occurrences of the legal turn `xy` in
`partial^-`. Then:

- there are `c_xy` darts of type `('-', x, y)`;
- there are `n_x = sum_y c_xy` darts of type `('+', x, i)`, one per block `R(x)`;
- there are `c_px` darts of type `('L', p, x)`.

This is the count equation of `lp_allwords.Types.count_coeffs`.

**Step 3: vertex polygons.** At a vertex `v` of valence `k`, list the outgoing darts
`d_1, ..., d_k` in cyclic order. Here `q_s = p(d_s)` is the paired dart and `d_{s+1} = next(q_s)`.
Project to the slots `(type d_s -> type q_s)`. The resulting cyclic list satisfies:

- `label(q_s) = label(d_s)^-1`, and `type d_{s+1}` is a successor of `type q_s` (by construction);
- the labels of `d_1, ..., d_k` lie in pairwise distinct gates (L). So the types are pairwise
  distinct, and rotating to put the smallest type first gives a canonical representative;
- `k <= 2 min(g_+, g_-)`: the gate bound, part 2 of `positive-f-folded-fatgraphs-have-only-even-valence`;
- at most one `d_s` is a `partial^-` dart (by (4), at most one `partial^-` corner per vertex);
- no slot has both `d_s` and `q_s` of `partial^-` type (by (4), no edge with `partial^-` on both sides);
- if some `d_s` is an `f`-dart, then `k = 2` and it is the only one (by (2) and (3)).

`lp_allwords.polygons` enumerates exactly the cyclic lists with these properties, with
`maxval = 2 min(g_+, g_-)`.

**Step 4: the linear system.** Let `y_P` be the number of vertices projecting to the polygon `P`.
Then:

- *(types)* for every type `tau`, `sum_P y_P #{s : d_s = tau} = count(tau)(c)` (Step 2);
- *(pairs)* for every pair of types `{tau, sigma}`, `sum_P y_P (#{tau -> sigma slots} - #{sigma -> tau slots}) = 0`.
  Every edge `{d, p(d)}` is seen once as the slot `d -> p(d)` at the vertex of `d`, and once as
  the slot `p(d) -> d` at the vertex of `p(d)`;
- *(circulation)* `c` is a circulation on legal turns, because `partial^-` is a union of cyclic words;
- *(homology)* `[partial^-] = sum_{xy} c_xy [x] = 0` (Step 1).

After scaling so that `sum c = 1`, `(y, c) >= 0` is a feasible point, and
`chi(X) = V - E = sum_P y_P (1 - k_P / 2)`. So a certificate for `phi` makes the LP feasible.

**Step 5: exact infeasibility.** `lp_allwords.farkas_infeasible` rounds a floating Farkas
vector, clears denominators to an integer vector `(z, t)`, and checks in exact integer
arithmetic that:

- `(A^T z)_P <= 0` on every polygon column;
- `(B^T z)_j + t <= 0` on every `c` column;
- `t > 0`.

For a feasible `(y, c)` this gives `0 = z^T (A y + B c) <= -t sum c = -t < 0`, which is a
contradiction. `census_allwords_m1.log` records verdict `infeasible-exact` for 6372 entries.
Every chunk completed; the per-chunk `stats` lines add up to `{infeasible-exact: 6372, NEGATIVE: 48}`.
By Step 4, none of these 6372 automorphisms has a legal `f`-folded fatgraph. This is part 1.

**Step 6: the 48 negative entries.** For each entry with verdict `NEGATIVE`, `surface_batch.py`
searches for an integral certificate with `partial^- = {w, w^-1}` over legal cyclic words `w` of
length 2. It uses the SAT search of `sat4.py`, and then the independent checker
`verify_surface.py`, which imports nothing from the search code. All 48 give
`independent=True CERTIFICATE OK` with `chi(X) = -2` and one component (`surfaces_m1_census.log`).
The certificate files are in `surfaces_m1/` and `surfaces_m1_census/`. The checker also verifies an
explicit inverse, `det M = ±1`, primitivity, and the absence of a rational root.

By `legal-f-folded-fatgraphs-give-surface-subgroups`, `S*_f(X)` is `pi_1`-injective. It is closed
and orientable, with `chi = -2`, as in Step 4 of
`hyperbolic-f3-by-z-with-genus-two-surface-certificates-proof`. This is part 2.

**Step 7: classes.** Relabelling letters by `s in S_3` conjugates `phi` by an automorphism.
Reversing all images is conjugation by `x -> x^-1` composed with `phi`. Both give isomorphic
mapping tori and transport certificates. `classes.py` canonicalises every entry under these 12
operations: 535 classes, and the 48 negative entries form 4 classes of size 12. This is part 3.

**Step 8: consistency of the projection.** `validate_certificates.py` rebuilds each of the 48
certificates in the dart order of `verify_surface.py`. It then checks that:

- labels, `f`-flags, kinds and successors agree with the types;
- every vertex orbit of `next o p` is an enumerated polygon;
- the integer point `(y, c)` satisfies `A y + B c = 0` exactly, with the certificate's `chi = -2`.

48 of 48 pass. This does not prove Step 4. It checks that the implementation does not exclude the
certificates that actually exist. This is part 4. `QED`
