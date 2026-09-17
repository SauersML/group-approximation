---
rg: 2
id: power-two-word-free-census-of-power-one-silent-classes-proof
kind: route
title: Run the word-free LP on the square of each power-one-silent class representative, with exact Farkas vectors, SAT boundary searches and the independent checker
target: power-two-word-free-census-of-power-one-silent-classes
requires:
  - legal-f-folded-fatgraphs-give-surface-subgroups
  - legal-folded-certificates-at-power-one-census
  - positive-f-folded-fatgraphs-have-only-even-valence
  - hyperbolic-f3-by-z-with-genus-two-surface-certificates
  - power-two-folded-fatgraphs-of-genus-k-plus-two-family
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp_allwords.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_allwords.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/m2_class_representatives.txt
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_allwords_m2_classes.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_batch.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_batch_lengths.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m2_census_negatives.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m2_new_negatives.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m2_partial.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m2_census
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surfaces_m2_census.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/validate_certificates.py
---

Notation: `phi` is a class representative from `m2_class_representatives.txt`, `f` is its rose map,
`M` is its matrix, and upper case is inverse.

Standard facts used, not re-read at source: Bestvina--Handel, Brinkmann, one-endedness of
free-by-cyclic groups, and invariance of the Alexander polynomial of a group with `b_1 = 1`
(up to units and `t <-> t^-1`).

**Step 1: power two is power one for `phi^2`.** `phi` is positive, so `phi^2` is positive and its
rose map is `f^2`, with no cancellation. `Df^2 = (Df)^2` has the same gates as `Df`. A legal
`f^2`-folded fatgraph is exactly a legal `g`-folded fatgraph for the rose map `g` of `phi^2`.
`census_allwords.py 2` builds the LP of `lp_allwords.py` for `phi^2`.

**Step 2: the projection is sound for `phi^2`.** Steps 1 to 4 of
`legal-folded-certificates-at-power-one-census-proof` show that a certificate gives a feasible
point of the LP. They use:

- positivity, which gives no cancellation along legal turns (Step 8 of
  `positive-f-folded-fatgraphs-have-only-even-valence-proof`), and the gate bound
  `k <= 2 min(g_+, g_-)` of that note. Both hold for `phi^2`;
- `det(I - M) != 0`. Here we need `det(I - M^2) = det(I - M) det(I + M) = -chi_M(1) chi_M(-1)`, up
  to sign. For a representative in the census, `chi_M` is an irreducible cubic, so
  `chi_M(±1) != 0`, and `[partial^-] = 0` follows as before.

So if the power-two LP is infeasible, `phi` has no legal `f^2`-folded fatgraph.

**Step 3: exact infeasibility (part 1).** `census_allwords.py 2 i i+1` was run for each of the 444
representatives, single-threaded, with `timeout 1200` and a 2 GB address-space limit. Every run
completed: there is no `chunk ... exit` line, and the entry set of `census_allwords_m2_classes.log`
equals `m2_class_representatives.txt`. For verdict `infeasible-exact`,
`lp_allwords.farkas_infeasible` has verified an integer vector `(z, t)` in exact arithmetic, with
`(A^T z)_P <= 0`, `(B^T z)_j + t <= 0` and `t > 0`. That contradicts feasibility, as in Step 5 of
the power-one proof. The `stats` lines add up to
`{infeasible-exact: 411, infeasible-float: 9, NEGATIVE: 24}`. With Step 2, this is part 1.
Part 2 lists the `infeasible-float` entries, and nothing is claimed for them.

**Step 4: certificates (part 3).** For each `NEGATIVE` entry the SAT search of `sat4.py` looks for a
pairing with `partial^- = {w, w^-1}`. The words `w` are the cyclically legal words of length 2
and 3 (`surface_batch.py`) and then 4 (`LENS=4 surface_batch_lengths.py`, the same program with
a different length list). A found pairing is re-checked by `sat4.verify4` and then by
`verify_surface.py`, which imports nothing from the search. `verify_surface.py` checks:

- an explicit inverse;
- the characteristic polynomial, and that it has no rational root;
- `M^k > 0` for some `k`;
- that the labels of every vertex lie in distinct gates of `f^2` (L), the conditions (2), (3) and
  (4), one component, and `chi(X)`.

For entries 3075, 3684, 4011, 4017 and 4052, `verify_surfaces_m2_census.log` records
`CERTIFICATE OK` on `surfaces_m2_census/phi<n>.json`, with the `chi(X)`, dart counts and `partial^-`
of the table. `validate_certificates.py` projects each of the five to a feasible LP point with the
same `chi` (summary lines `0 failures`), which cross-checks Step 2 on these examples. Entries 300 and
672 are certified in `power-two-legal-folded-certificates-reach-beyond-power-one` and
`power-two-folded-fatgraphs-of-genus-k-plus-two-family` (k = 3 and k = 2).

By `legal-f-folded-fatgraphs-give-surface-subgroups` applied to `f^2`, `S*_{f^2}(X)` is a closed
orientable surface with `chi = chi(X)`, of genus `1 - chi(X)/2`, and it is `pi_1`-injective in
`F x|_{phi^2} Z`. That group is the index-2 subgroup of `G = F x|_phi Z` generated by `F` and
`t^2`. So `G` contains the surface group. The genera are 5 for `chi = -8` (3075) and 3 for
`chi = -4` (3684, 4011, 4017 and 4052).

**Step 5: hyperbolicity.** For each table entry, the checker confirms that `M^k > 0` and that
`chi_M` is a cubic with no rational root, hence irreducible, with a Perron--Frobenius root
`> 1`. Step 2 of `hyperbolic-f3-by-z-with-genus-two-surface-certificates-proof` uses only these
facts. So `phi` is fully irreducible and atoroidal, and `G` is one-ended and hyperbolic.

**Step 6: invariants (part 4).** `b_1(G) = 1`, `H_1(G) = Z ⊕ coker(M - I)`, and
`|coker(M - I)| = |chi_M(1)|`. This gives 2 for `t^3 - 3t^2 - t + 1` and 4 for
`t^3 - 3t^2 - t - 1`. The Alexander polynomial is `chi_M`. The reciprocals, normalised to be monic,
are `t^3 - t^2 - 3t + 1` and `t^3 + t^2 + 3t - 1`. The earlier rank-3 certificates have:

- power one: `t^3 - t^2 - 5t + 1` and `t^3 - 2t^2 - 6t + 1`;
- the rank-3 family: `t^3 - (i+j+1)t^2 - (i+3j+5)t + 1` with `i, j >= 0`, whose linear
  coefficient is `<= -5`;
- the power-two family: `t^3 - t^2 - (2k+3)t + 1` with `k >= 1`, whose linear coefficient is
  `<= -5`.

None of these matches either polynomial or its reciprocal. The linear coefficients are `-1`, `-3`
and `+3`, and the constant term `-1` never occurs before. The every-rank family has degree `>= 4`.
Every earlier `|T|` is `2(i + 2j + 2) >= 4`, `2k + 2 >= 4`, 4 or 6. This is part 4.

**Step 7: open entries (part 5).** `surfaces_m2_partial.log` (entries 61 to 464),
`surfaces_m2_new_negatives.log` (939, 1632, 1633, 1635 and 1744) and
`surfaces_m2_census_negatives.log` (the rest, and all `|w| = 4` runs) record
`no-certificate-with-length<=3` and `no-certificate-with-length-in-4` for the 17 listed entries.
A SAT answer of unsatisfiable, after the cycle-cutting loop of `sat4.solve4`, means that no
pairing exists for that boundary. Each run finished, with no `exit` line. A run that stops at the
iteration cap is also recorded as no certificate. So part 5 is a statement about what the search
found, not an impossibility claim. `QED`
