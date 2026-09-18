---
rg: 2
id: power-two-legal-folded-certificates-reach-beyond-power-one
kind: claim
title: The hyperbolic mapping torus of a -> abb, b -> caaa, c -> babb has no legal f-folded fatgraph at power one but a legal f^2-folded fatgraph of genus five, so powers of the criterion reach new groups
distinct_from:
  legal-folded-certificates-at-power-one-census: that decides power one on the whole census and leaves higher powers open; this exhibits a census automorphism with no power-one certificate at all and a verified power-two certificate.
  hyperbolic-f3-by-z-with-genus-two-surface-certificates: that certifies two groups at power one with genus 2 (torsion of H_1 of order 4 and 6); this certifies a group with torsion of order 8, not isomorphic to those, and it needs power 2 and genus 5.
  hyperbolic-fn-by-z-genus-two-surfaces-every-fibre-rank: that reuses one power-one certificate in every fibre rank; this shows that the power parameter of the criterion is not redundant.
  legal-f-folded-fatgraphs-give-surface-subgroups: that is the criterion, with an arbitrary power m; this is the first instance where m = 2 certifies a group that m = 1 does not reach through the same representative.
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for all one-ended hyperbolic groups; this adds one explicit hyperbolic F_3 x| Z and its 11 relabelled or reversed variants.
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_phi300_m2.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface_phi300_m2.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/validate_certificates.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_allwords_m1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_allwords_m2_partial.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_batch.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surfaces_m2_partial.log
---

**ESTABLISHED (computer-certified).** Proof in
`power-two-legal-folded-certificates-reach-beyond-power-one-proof`.

Let `F = F(a, b, c)` and let `f` be the rose map of

```text
phi_300 : a -> abb,  b -> caaa,  c -> babb      (chi_M = t^3 - t^2 - 9t + 1)
```

This is entry 300 of the census `phi_scan4.json` of `legal-folded-certificates-at-power-one-census`.

1. `phi_300` is an automorphism, with inverse `b -> cA`, `a -> aaCaC`, `c -> b (cAcAA)^3`. The
   mapping torus `G_300 = F x|_phi Z` is one-ended and hyperbolic.
2. **Power one gives nothing.** An exact integer Farkas vector makes the word-free LP at `m = 1`
   infeasible (`census_allwords_m1.log`, entry 300, `infeasible-exact`). So there is no legal
   `f`-folded fatgraph over this rose representative, whatever its boundary.
3. **Power two gives genus 5.** `surface_phi300_m2.json` is a legal `f^2`-folded fatgraph `X`:
   - `partial^- = {bc, CB}`, so `partial^+` reads `f^2(bc)^-1` and `f^2(CB)^-1`, which are
     28 letters each;
   - 60 darts, `V = 22` (14 vertices of valence 2 and 8 of valence 4), `E = 30`, one component,
     `chi(X) = -8`.

   By `legal-f-folded-fatgraphs-give-surface-subgroups` applied to `f^2`, `S*_{f^2}(X)` is a
   closed orientable surface of genus 5 that is `pi_1`-injective in `F x|_{phi^2} Z`. That group
   has index 2 in `G_300`, so `G_300` contains the genus-5 surface group.
4. **A new group.** `H_1(G_300) = Z ⊕ T` with `|T| = |chi_M(1)| = 8`. For the four power-one
   classes of the census, `|T|` is 4 (`t^3 - t^2 - 5t + 1`) or 6 (`t^3 - 2t^2 - 6t + 1`). So
   `G_300` is not isomorphic to any group certified at power one. The same holds for the 12
   members of its class under relabelling and reversal.

## Why it matters

- At power one the criterion is silent on 6372 of the 6420 census automorphisms. Whether the
  power `m` in the criterion adds anything was open (`legal-folded-certificates-at-power-one-census`,
  Scope). It does: the certified set strictly grows from `m = 1` to `m = 2`.
- The certificate is still small and local. It has two boundary words of length 2 and genus 5,
  and it passes the same independent checker as the power-one certificates.
- A census at `m = 2` is therefore worth finishing. Every LP-negative entry is a candidate.

## Evidence

- `verify_surface_phi300_m2.log`:
  - `verify_surface.py` passes (`CERTIFICATE OK`). It checks the explicit inverse, `M^3 > 0`,
    the cubic with no rational root, (L), (2), (3), (4), connectivity and `chi(X) = -8`;
  - `validate_certificates.py` projects the certificate to a feasible point of the `m = 2` LP
    with the same `chi`.
- `sat4.verify4` (independent code, called by `surface_batch.py`) also passes, including the
  unrolled graphs `X_n` for `n <= 2`.

## Partial power-two census

The `m = 2` word-free LP has now been run on 53 of the 444 class representatives that are
infeasible at `m = 1` (`census_allwords_m2_partial.log`):

- 44 are `infeasible-exact`;
- entries 333 and 412 are infeasible in floating point only, with no exact Farkas vector yet;
- 7 are LP-negative: 61, 108, 198, 228, 300, 414 and 464.

`surface_batch.py` finds a certificate with `partial^- = {w, w^-1}` and `|w| <= 3` for entry 300
only (`surfaces_m2_partial.log`). The LP optimum is `-2` there, and between `-1.5` and `-0.8` for
the other six.

## Scope

- One group (one class of 12 automorphisms). It is not a statement about all automorphisms.
- Part 2 is about this rose representative only. Another train-track representative of `phi_300`,
  or of a power of it, could carry a power-one certificate. So the claim is about the reach of the
  certificate method with the representative fixed, not about intrinsic invariants.
- For the six other LP-negative entries, `m = 2` is still undecided.
