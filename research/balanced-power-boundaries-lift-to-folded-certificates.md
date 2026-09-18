---
rg: 2
id: balanced-power-boundaries-lift-to-folded-certificates
kind: claim
title: A legal f-folded fatgraph whose boundary circles are powers with balanced root exponents has a finite cover that is a certificate, so the per-word polygon LP is exact and entries 939 and 4010 contain surface groups
distinct_from:
  legal-f-folded-fatgraphs-give-surface-subgroups: that is the criterion, and it needs a fatgraph whose boundary is already matched circle by circle; this builds such a fatgraph from one whose boundary is balanced only on average, by finite covers.
  positive-f-folded-fatgraphs-have-only-even-valence: that shows the per-word LP of lp5.py is a necessary condition; this proves the converse, so every rational feasible point with chi < 0 gives a surface subgroup.
  power-two-word-free-census-of-power-one-silent-classes: that certifies eight classes at power two and leaves 16 LP-negative entries open; this certifies entries 939 and 4010, which leaves 14 open.
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for all one-ended hyperbolic groups; this reduces the certificate question for a train-track mapping torus to rational linear programming over finite word sets, and adds two explicit hyperbolic F_3 x| Z.
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lift_lp.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lift_word.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface_multi.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m2_census/phi939.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m2_census/phi4010.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface_phi939_phi4010_m2.log
---

**ESTABLISHED.** Proof in `balanced-power-boundaries-lift-to-folded-certificates-proof`.

**Setting.** Let `phi` be an automorphism of `F = F(x_1, ..., x_n)` whose rose map `f`
satisfies (TT) of `legal-f-folded-fatgraphs-give-surface-subgroups`. Every positive
automorphism does. Replace `f` by a power `f^m` throughout.

A *balanced power fatgraph* is a finite fatgraph `X` over the rose, which may be
disconnected, together with:

- a mark `-` or `+` on each boundary circle;
- for each `+` circle `C`, a cyclic word `y_1 ... y_L` in the letters. The circle reads
  `f(y_L)^{-1} ... f(y_1)^{-1}` cyclically, and its `f`-corners sit exactly at the
  block starts.

It must satisfy the following conditions.

- **(L), (2), (3), (4).** These are the local conditions of the criterion, in the form
  of `lp5.py`.
  - The directions at a vertex lie in pairwise distinct gates.
  - A vertex with an `f`-corner is 2-valent.
  - A vertex has at most one `f`-corner and at most one `partial^-` corner.
  - No edge has `partial^-` on both sides.
- **(P) Powers.**
  - Every `-` circle reads a cyclically reduced cyclic word `u_C^{e_C}`, with `u_C` not a
    proper power.
  - Every `+` circle has `y_1 ... y_L = v_C^{e_C}`, with `v_C` not a proper power and
    `f(v_C)` cyclically reduced.
- **(B) Balance.** For every primitive cyclic word `u`, the sum of `e_C` over the `-`
  circles with `u_C = u` equals the sum of `e_C` over the `+` circles with `v_C = u`.
- `chi(X) < 0`.

**Theorem.** A balanced power fatgraph `X` has a finite cover `X~ -> X` of degree `3D`,
with `D` even. The cover `X~` is a legal `f`-folded fatgraph whose boundary is matched:
each `partial^-` circle reading `w` is paired with a `partial^+` circle reading
`f(w)^{-1}`, with its `f`-corners at the block starts. Moreover `chi(X~) = 3D chi(X) < 0`.
So `F x|_phi Z` contains a closed orientable surface group of genus `>= 2`.

There is no annulus caveat. Annular components are allowed, because by (P) their two
circles automatically have equal exponents.

**Corollary (the per-word LP is exact).** Let `W` be a finite set of cyclically reduced
words such that every `f(w)`, `w` in `W`, is cyclically reduced. Let `B = Boundary(phi^m, W)`
be the boundary of `ffold.py`, and let `polygons(B)` be the vertex polygons of `lp5.py`.
Consider the system in variables `y_P >= 0` (polygons) and `n_w >= 0` (words):

- for each dart `d` of the two circles of `w`, the number of slots of the `y`-weighted
  polygons that start at `d` equals `n_w`;
- for each pair `{d, q}`, the weights of the slots `d -> q` and `q -> d` agree.

If this system has a rational solution with `sum_P y_P (1 - |P|/2) < 0`, then `F x|_phi Z`
contains a closed surface group. In particular, a `NEGATIVE` line of `lp5.py` (one word,
`n_w = 1`) now certifies a surface subgroup. Before this it was only a candidate.

Every certificate with boundary made of `N` copies of `(w, f(w)^{-1})` projects to a
feasible point with the same `chi`. This is Step 8 of
`positive-f-folded-fatgraphs-have-only-even-valence-proof`, for positive `phi` and a legal
cyclic word `w`. So for such `phi` and `w`, some certificate with boundary made of copies
of `w` exists if and only if the rational LP of `lp5.py` has minimum `chi < 0`.

**Application: census entries 939 and 4010 (power 2).** Both are LP-negative entries of
`power-two-word-free-census-of-power-one-silent-classes` that the SAT boundary search did
not reach. Both certificates came from the positions construction of the proof applied to
an integer solution of the word-free LP, followed by `lift_lp.py --perm`.

| entry | `phi` | `partial^-` | darts | `V` | `E` | `chi(X)` | components of `X` | genus | `chi_M` |
|---|---|---|---|---|---|---|---|---|---|
| 939 | `a -> ab, b -> bca, c -> caab` | `AA, AA, BCBC, BCBC, aa, aa, bcbc, bcbc` | 224 | 88 | 112 | `-24` | 1 | 13 | `t^3 - 3t^2 + t - 1` |
| 4010 | `a -> ab, b -> babc, c -> abb` | `AC, B, ac, b` | 64 | 28 | 32 | `-4` | 2 (`S*_f(X)` connected) | 3 | `t^3 - 3t^2 - t + 1` |

For both entries, `verify_surface_multi.py` gives `CERTIFICATE OK`. It checks:

- an explicit inverse of `phi`;
- `M^2 > 0`;
- a cubic `chi_M` with no rational root;
- (L), (2), (3), (4);
- that the closed surface is connected;
- `chi(X)`.

For entry 939, `verify_surface.py` also gives `CERTIFICATE OK`, since its `X` is connected.
`validate_certificates.py` projects both certificates to feasible points of the power-two
LP with the same `chi` (`0 failures`). The outputs are in
`verify_surface_phi939_phi4010_m2.log`. So both `F_3 x| Z` are one-ended and hyperbolic and
contain closed surface groups of genus 13 and 3 respectively, and `|chi_M(1)| = 2` in both.

## Why it matters

- **It removes the matching step.** Until now a certificate had to be found with the
  boundary matched circle by circle, by SAT (`sat4.py`) or by a hand construction. The
  theorem only asks for local polygons and linear balance of exponents. Those are exactly
  what an LP controls.
- **It is a strict reduction.** For a train-track mapping torus, a surface subgroup
  follows from one rational LP point with `chi < 0`, for any finite word set `W`. For one
  word this condition is also necessary for certificates with boundary made of copies of
  that word.
- **The gap to the word-free LP is now precise.** The word-free LP of `lp_allwords.py`
  relaxes (B) to letter counts. Negative word-free points that do not come from a balanced
  point are the only remaining obstruction to realising them.

## Scope

- The theorem needs (P) and (B), with the roots taken from the actual circle readings. A
  word-free integer point satisfies (B) when its turn support is a permutation. That is
  how `lift_lp.py --perm` produced both certificates, and the certificates are checked
  independently. The general word-free point is not covered.
- 14 LP-negative power-two entries remain open: 61, 108, 198, 228, 464, 1632, 1633, 1635,
  1744, 2298, 2429, 4012, 4485 and 4887. See the census node's `## Attempts` for what was
  tried on them.
