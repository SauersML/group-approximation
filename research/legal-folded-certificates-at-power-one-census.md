---
rg: 2
id: legal-folded-certificates-at-power-one-census
kind: claim
title: Among 6420 positive automorphisms of F_3 with short images, exactly 48 have a legal f-folded fatgraph with chi < 0, all certified genus two; the other 6372 have no legal f-folded fatgraph at all
distinct_from:
  positive-f-folded-fatgraphs-have-only-even-valence: that LP fixes one boundary word w and certifies two automorphisms word by word; this LP has no boundary word, decides every boundary at once, and runs on all 6420 automorphisms of that census.
  hyperbolic-f3-by-z-with-genus-two-surface-certificates: that exhibits certificates for two classes; this shows that at power one there are exactly four certified classes in the census and that nothing else in it has any certificate.
  legal-f-folded-fatgraphs-give-surface-subgroups: that is the criterion; this measures where its power-one certificates exist.
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for all one-ended hyperbolic groups; this gives surface subgroups for 48 hyperbolic F_3 x| Z and shows the criterion at power one is silent on the rest of the census.
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp_allwords.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_allwords.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_allwords_m1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/classes.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_batch.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m1_census.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m1_census
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m1
  - experiments/legal-f-folded-fatgraphs-2026-09-17/validate_certificates.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/validate_certificates_m1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/phi_scan4.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/m2_class_representatives.txt
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_allwords_m2_partial.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m2_partial.log
---

**ESTABLISHED (computer-certified).** Proof in `legal-folded-certificates-at-power-one-census-proof`.

`phi_scan4.json` is the census of `positive-f-folded-fatgraphs-have-only-even-valence`, part 5. It
holds 6420 positive automorphisms `phi` of `F(a, b, c)` with images of length 2--4. Each is
primitive, has an irreducible characteristic polynomial, and has at least 4 gates. So each
mapping torus `F_3 x|_phi Z` is one-ended and hyperbolic.

Let `f` be the rose map of `phi`. A *certificate* is a legal `f`-folded fatgraph: an `f`-fatgraph
satisfying (L), (2), (3), (4) of `legal-f-folded-fatgraphs-give-surface-subgroups`. It may have
any number of boundary words, of any length. At power `m = 1`:

1. **No certificate at all for 6372 automorphisms.** For each of them an exact integer
   Farkas vector proves the word-free LP of `lp_allwords.py` infeasible. So no legal
   `f`-folded fatgraph exists, whatever its boundary or Euler characteristic. This includes the
   1044 automorphisms that the gate bound already kills.
2. **Genus-two certificates for the other 48.** For each of them the LP minimum of `chi`
   (normalised by `sum c = 1`) is `-1/2`. `surface_batch.py` finds a certificate with
   `partial^- = {w, w^-1}`, `|w| = 2` and `chi(X) = -2`. The independent checker
   `verify_surface.py` passes on all 48 (`surfaces_m1_census.log`). By the criterion, each
   of these 48 groups contains a closed genus-2 surface group.
3. **Four classes.** Under relabelling of letters and reversal of images (both give isomorphic
   mapping tori and carry certificates to certificates), the 48 form 4 classes of 12
   (`classes.py`). The class representatives are:

   | census entry | canonical form | `chi_M` |
   |---|---|---|
   | 192 | `a -> abb, b -> caba, c -> babb` | `t^3 - 2t^2 - 6t + 1` |
   | 1023 | `a -> abb, b -> ca, c -> babb` | `t^3 - t^2 - 5t + 1` |
   | 2441 | `a -> bab, b -> abac, c -> bbab` | `t^3 - 2t^2 - 6t + 1` |
   | 6264 | `a -> bab, b -> ac, c -> bbab` | `t^3 - t^2 - 5t + 1` |

   The first two are the automorphisms of `hyperbolic-f3-by-z-with-genus-two-surface-certificates`.
4. **Consistency check of the LP.** `validate_certificates.py` projects each of the 48
   integral certificates to the LP types. Every vertex is an enumerated polygon, and the
   projected point satisfies every equation exactly with the certificate's `chi`
   (`validate_certificates_m1.log`: 48 of 48).

**Why it matters.** Part 1 is an obstruction on a large, explicit class: at power one the legal
criterion gives nothing for 99.25% of the census, and the obstruction covers every boundary. It
does not say those groups lack surface subgroups. Part 2 says the certified groups are
not rare accidents, and that the LP is sharp: every LP-negative entry has a certificate with the
smallest possible boundary.

**Scope.** Only power `m = 1` and the 6420 automorphisms of `phi_scan4.json`. Higher powers
`f^m` have the same gates but longer blocks, and more polygons can close. They are not decided on the census. A run at
`m = 2` on the 444 class representatives that are infeasible at `m = 1`
(`m2_class_representatives.txt`) takes up to about 500 s per entry. The first 53 have been run
(`census_allwords_m2_partial.log`):

- 44 are `infeasible-exact`, and 2 are infeasible in floating point only;
- entries 61, 108, 198, 228, 300, 414 and 464 are LP-negative.

`surface_batch.py` finds an `f^2`-folded legal fatgraph with `partial^- = {w, w^-1}`, `|w| <= 3`,
for entry 300 only (`surfaces_m2_partial.log`). That one has genus 5
(`power-two-legal-folded-certificates-reach-beyond-power-one`). So `m = 2` certifies strictly more
than `m = 1`, and the other six LP-negative entries are open.
