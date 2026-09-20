---
rg: 2
id: pure-braid-open-zero-twist-cones-lie-in-sigma-two-of-p5
kind: claim
title: "Explicit open cones of zero-sum characters of P_5, one on the twist hyperplane c_12 = 0 and one on c_123 = 0, lie in Sigma^2(P_5)"
distinct_from:
  pure-braid-nonresonant-zero-twist-characters-in-sigma: that claim asks for every non-resonant zero-sum character on every twist hyperplane, for all n and all 2 <= m <= n-3; this proves Sigma^2(P_5) only on two explicit open cones, one in each S_6-orbit of twist hyperplanes.
  pure-braid-nonzero-twist-characters-lie-in-sigma-n-minus-3: that claim covers characters with every twist value nonzero; the two base characters here have c_12 = 0, respectively c_123 = 0, so they are outside its region.
  pure-braid-twist-depth-d-characters-lie-in-sigma-n-3-d: that claim gives only Sigma^1(P_5) for twist depth 1; this gives Sigma^2(P_5) for the two base characters here, which have twist depth at least 1.
  pure-braid-kohno-pajitnov-cones-miss-twist-hyperplanes: that claim shows that Kohno–Pajitnov cones never meet the twist hyperplanes; the cones here do meet them, and they are found by a different method.
artifacts:
  - experiments/pure-braid-translated-jump-loci-2026-09-17/cert_n5_m2_t5c01.json
  - experiments/pure-braid-translated-jump-loci-2026-09-17/cert_n5_m2_t5c123w.json
  - experiments/pure-braid-translated-jump-loci-2026-09-17/verify_cert.py
  - experiments/pure-braid-translated-jump-loci-2026-09-17/salvetti_morse.py
  - experiments/pure-braid-translated-jump-loci-2026-09-17/verify_cert_n5_m2_t5c01.log
  - experiments/pure-braid-translated-jump-loci-2026-09-17/verify_cert_n5_m2_t5c123w.log
  - experiments/pure-braid-translated-jump-loci-2026-09-17/margin.py
  - experiments/pure-braid-translated-jump-loci-2026-09-17/margin_t5c01.log
  - experiments/pure-braid-translated-jump-loci-2026-09-17/margin_t5c123w.log
  - experiments/pure-braid-translated-jump-loci-2026-09-17/check_chars.py
  - experiments/pure-braid-translated-jump-loci-2026-09-17/check_chars_certified.log
  - experiments/pure-braid-translated-jump-loci-2026-09-17/antistar_check.py
  - experiments/pure-braid-translated-jump-loci-2026-09-17/antistar_check_n5.log
---

Write a character of `P_5` as `chi = sum a_ij omega_ij`, where `omega_ij` is dual to the
Artin generator `A_ij`. List the coefficients in the pair order
`12, 13, 14, 15, 23, 24, 25, 34, 35, 45`. The strands are 1-indexed here. The
certificate files are 0-indexed.

- `chi_1 = (0, 25, 19, -34, -3, 27, 10, 30, 24, -98)`.
  - Sum 0.
  - The only vanishing twist value is `c_12 = a_12 = 0`. This is the `2|4` split.
  - The Aomoto complex has `H^0 = H^1 = H^2 = 0` over `F_p` for two primes, so
    `chi_1` is not a real point of `R^{<=2}(P_5)`.
- `chi_2 = (5, -12, 19, -33, 7, 27, 10, 30, 24, -77)`.
  - Sum 0.
  - The only vanishing twist value is `c_123 = a_12 + a_13 + a_23 = 0`. This is the
    `3|3` split.
  - The Aomoto complex has `H^{<=2} = 0` as well.

These data are in `check_chars_certified.log`, which covers every `A` with
`2 <= |A| <= 4`.

**Claim.** Every character `chi = sum a_ij omega_ij` with `max |a_ij - (chi_1)_ij| < 0.0149`
lies in `Sigma^2(P_5)`. So does every character within `0.0422` of `chi_2` in the same
norm, and so does every positive multiple of any of these characters. In particular:

- a nonempty, relatively open cone of zero-sum characters on the hyperplane `c_12 = 0`
  lies in `Sigma^2(P_5)`;
- a nonempty, relatively open cone of zero-sum characters on the hyperplane `c_123 = 0`
  lies in `Sigma^2(P_5)`.

Here `Sigma^2 = Sigma^{n-3}` for `n = 5`. The exact radii are `29867/2000000` and
`42251/1000000`.

Before this claim, the graph had no character with a vanishing twist value in
`Sigma^2(P_5)`. The curve-complex criterion fails at level `n - 3` at every zero vertex
(see the 2026-09-16 attempts on `pure-braid-nonresonant-zero-twist-characters-in-sigma`).
The twist-depth criterion gives only `Sigma^1`.

The claim is the smallest case (`n = 5`, `m = 2`) of
`pure-braid-nonresonant-zero-twist-characters-in-sigma`, on open subsets of the two
twist hyperplanes. Strand permutations are automorphisms of `P_5` by conjugation in
`B_5`, and they act on the coefficients by `a_ij -> a_{s(i)s(j)}`. So the claim also
gives open cones on every hyperplane `c_A = 0` with `|A| = 2` or `|A| = 3`.

**Method (route `pure-braid-zero-twist-cones-p5-salvetti-morse-certificates`).**
The proof uses Bestvina–Brady Morse theory on the universal cover of the Salvetti
complex of the braid arrangement.

1. The heights are `f(D) = K * (sum of a_ij over walls separating D from the base
   chamber of the cell) + eta(D)`. The integer tie-break `eta` is recorded in the
   certificate file.
2. The ascending link of each of the 120 chambers is the order complex of an explicit
   poset `Asc(C)`.
3. `verify_cert.py` recomputes each `Asc(C)` in exact arithmetic from the Salvetti face
   rule. For each one it:
   - checks reduced `H_0 = H_1 = 0` over `F_1000003` and `F_32003`;
   - checks `pi_1 = 1` by simplifying an edge-path presentation to the empty
     presentation.

   The log line for all 120 chambers ends in "pi1 trivial", and the verdict is
   "VERIFIED".
4. The lowest-vertex assignment is an open condition in `a`. `margin.py` computes the
   radius over which it is unchanged.

Status: UNREVIEWED (swarm-0917 worker w20-z-last1, 2026-09-17). The proof is complete
modulo the imports named in the route: Salvetti's cell model, and the Bux–Gonzalez
criterion with the Morse Lemma. It is computer-assisted, and the verifier is
independent of the search code.
