---
rg: 2
id: power-two-folded-fatgraphs-of-genus-k-plus-two-family
kind: claim
title: For every k >= 1 the hyperbolic mapping torus of a -> abb, b -> c a^k, c -> babb contains a genus-(k+2) surface group, via a closed-form legal f^2-folded fatgraph that is checked for all k at once
distinct_from:
  power-two-legal-folded-certificates-reach-beyond-power-one: that certifies the single automorphism a -> abb, b -> caaa, c -> babb at power two with a solver-found pairing; this gives a pairing in closed form for the whole family phi_k (phi_3 is that automorphism), checks it for all k by affine symbolic arithmetic, and shows power one is silent for every k from 2 to 30.
  hyperbolic-f3-by-z-family-with-genus-two-surfaces: that reuses one fixed 16-letter pairing of genus 2 at power one; here the fatgraph grows with k (12k + 24 darts, genus k + 2), needs power two, and its groups have Alexander polynomials t^3 - t^2 - (2k+3) t + 1, which occur in that family only for k = 1.
  hyperbolic-fn-by-z-genus-two-surfaces-every-fibre-rank: that varies the fibre rank with one power-one certificate; this stays in rank 3 and varies the certificate itself.
  legal-f-folded-fatgraphs-give-surface-subgroups: that is the criterion; this is the first infinite family where the criterion is applied at power two, with certificates of unbounded size.
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for all one-ended hyperbolic groups; this adds infinitely many pairwise non-isomorphic hyperbolic F_3 x| Z whose rose representatives carry no power-one certificate.
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_certificates.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_certificates.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_symbolic.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_symbolic.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_m1_lp.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/power_two_family_m1_lp.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp_allwords.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_allwords_m2_classes_first171.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_batch.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m2_new_negatives.log
---

**ESTABLISHED (computer-certified for all k).** Proof in
`power-two-folded-fatgraphs-of-genus-k-plus-two-family-proof`.

Let `F = F(a, b, c)`, let `k >= 1`, and let `f_k` be the rose map of

```text
phi_k : a -> abb,  b -> c a^k,  c -> babb        chi_k(t) = t^3 - t^2 - (2k+3) t + 1.
```

1. `phi_k` is a positive automorphism, with inverse `a -> aaCaC`, `b -> cA`, `c -> b (cAcAA)^k`.
   `G_k = F x|_{phi_k} Z` is one-ended and hyperbolic.
2. **A closed-form power-two certificate.** Take `partial^- = {bc, CB}`. The boundary circles
   `f_k^2(bc)^-1` and `f_k^2(CB)^-1` have `6k + 10` letters each, and 15 affine rules in `k` pair
   the `12k + 24` letters (table in the proof note). The result is a legal `f_k^2`-folded fatgraph
   `X_k` with `4k + 10` vertices (`2k + 2` of valence 4, the rest of valence 2), `6k + 12` edges,
   one component and `chi(X_k) = -2k - 2`.
3. **Surface subgroups.** By `legal-f-folded-fatgraphs-give-surface-subgroups` applied to `f_k^2`,
   `G_k` has an index-2 subgroup `F x|_{phi_k^2} Z` containing `pi_1` of the closed orientable surface
   of genus `k + 2`. So `G_k` contains it too.
4. **Infinitely many groups.** `H_1(G_k) = Z ⊕ T_k` with `|T_k| = 2k + 2`, so the `G_k` are
   pairwise non-isomorphic. For `k >= 2` the Alexander polynomial `chi_k` also separates `G_k` from
   the mapping tori of the earlier legal-criterion nodes, except `G_3 = G_300`.
5. **Power one is silent.** For every `2 <= k <= 30`, the word-free LP at power one is infeasible
   with an exact Farkas vector (`power_two_family_m1_lp.log`). So `f_k` carries no legal
   `f_k`-folded fatgraph with any boundary. (`phi_1` is `phi_1` of
   `hyperbolic-f3-by-z-with-genus-two-surface-certificates`, which is certified at power one.)

## How it is checked for all k

- `power_two_family_symbolic.py` treats positions as affine functions of `k` and of a template
  parameter `i`, on regions `k >= 3`, `lo(k) <= i <= hi(k)`. It checks, with exact rational
  arithmetic:
  - every rule inversion is integer-affine;
  - every step `sigma = next o p` of 19 vertex templates;
  - that labels come from a periodic segment table;
  - that `p` pairs inverse letters;
  - (L), (2), (3) and (4) on every template;
  - the total template size `12k + 24` and the pair count `6k + 12`.

  Together with the coverage table of the proof note, this gives the vertex structure of `X_k`
  for all `k >= 3` (`power_two_family_symbolic.log`, ending `SYMBOLIC CERTIFICATE OK`).
- `power_two_family_certificates.py` builds `X_k` from the same formulas and runs the independent
  checker `verify_surface.py` for `1 <= k <= 200`. It checks the explicit inverse, the closed form
  of `chi_k`, `M^3 > 0`, (L), (2), (3), (4), connectivity and `chi = -2k - 2`. Result: 200 of 200
  (`power_two_family_certificates.log`). This covers `k = 1, 2`, and it cross-checks the symbolic
  run.
- The pairing was read off from SAT-solver certificates for `k = 2, ..., 7` and then guessed in
  closed form. For `k = 2, 3, 5` the formula reproduces the solver's pairing exactly.

## Why it matters

- Before this node, every legal-criterion certificate on main had bounded size: genus
  2, or genus 5 for `G_300`. Here a certificate *family* of unbounded genus is proved for
  infinitely many automorphisms at once, at a power where power one provably fails.
- The proof method generalises. Boundary words of `f^m(w)` for a family `phi_k` are periodic
  segments in `k`, so a pairing that is affine in `k` is checked by finitely many affine
  inequalities. Such a pairing is guessed from a few solver certificates. This turns the
  solver-plus-checker pipeline into a way to prove infinite families.
- Census entry 672 (`phi_2`) is one of the LP-negative entries of the power-two census
  (`census_allwords_m2_classes_first171.log`). It is now certified.

## Power-two census status

The `m = 2` word-free LP has now run on 171 of the 444 class representatives that are infeasible
at `m = 1` (`census_allwords_m2_classes_first171.log`):

- 152 are `infeasible-exact`;
- 6 are `infeasible-float`;
- 13 are LP-negative: 61, 108, 198, 228, 300, 414, 464, 672, 939, 1632, 1633, 1635 and 1744.

Of the LP-negative entries, 300 and 672 are certified (both are members of this family). For 672
`surface_batch.py` also finds its own genus-4 certificate (`surfaces_m2_new_negatives.log`). It
finds no certificate with `partial^- = {w, w^-1}` and `|w| <= 3` for 939, 1632, 1633, 1635 and
1744 (same log), nor for the six other entries (`surfaces_m2_partial.log` of
`power-two-legal-folded-certificates-reach-beyond-power-one`). So 11 entries are open at `m = 2`.

## Scope

- Part 5 is checked for `k <= 30` only, and it concerns the rose representative `f_k`.
- Part 4 distinguishes groups by `H_1` and the Alexander polynomial. It does not say whether some
  `G_k` is commensurable with an earlier group.
- The symbolic checker is a program. The proof note states the rule and template tables and proves
  coverage by hand. The program checks each template on its symbolic region, and it is
  cross-checked against the independent numeric checker for `k <= 200`.
