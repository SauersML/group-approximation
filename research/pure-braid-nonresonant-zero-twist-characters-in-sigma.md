---
rg: 2
id: pure-braid-nonresonant-zero-twist-characters-in-sigma
kind: claim
title: "Non-resonant zero-sum characters of P_n with a vanishing Dehn twist value lie in Sigma^m(P_n) for 2 <= m <= n-3"
distinct_from:
  pure-braid-bnsr-complements-are-real-resonance-varieties: that claim is the equality Sigma^m = complement of R^{<=m} for all n and m; this is only its hard direction on the twist hyperplanes in the middle range, which together with proved claims implies it.
  bf-n-r-twist-invisible-restrictions-nonresonant: that claim asks that specific characters Phi_k avoid resonance; this assumes non-resonance and asks for membership in Sigma^m.
  pure-braid-twist-depth-d-characters-lie-in-sigma-n-3-d: that proved claim gives Sigma^{n-3-d} from twist depth alone and is not sharp; this asks for the level dictated by resonance.
---

Let `n >= 5` and `2 <= m <= n - 3`. Let `chi = sum a_ij omega_ij` be a character of
`P_n` such that:

- `sum_{i<j} a_ij = 0`;
- `c_A(chi) = sum_{i<j in A} a_ij = 0` for some `A <= [n]` with `2 <= |A| <= n - 1`;
- `H^i(A(P_n) ⊗ R, chi ∧) = 0` for all `i <= m`, where `A(P_n)` is the
  Orlik–Solomon algebra of the braid arrangement (so `chi` is not a real point of
  `R^{<=m}(P_n)`).

Claim: `[chi]` lies in `Sigma^m(P_n)`.

The smallest case is `n = 5`, `m = 2`. Zero-sum characters are characters of
`H_5 = PMod(S_{0,6})`, and `S_6` permutes the twist hyperplanes. Up to that
symmetry there are two of them: `c_12 = 0` (split `2|4`) and `c_123 = 0` (split
`3|3`).

## Attempts

- 2026-09-16 (swarm lane pure-braid-bnsr-complements; artifact
  `research/artifacts/pure-braid-twist-nonvanishing-sigma-2026-09-16.md`).
  - Covered by twist depth. `pure-braid-twist-depth-d-characters-lie-in-sigma-n-3-d`
    gives `Sigma^m` whenever `d(chi) <= n - 3 - m`. What remains is
    `d(chi) >= n - 2 - m`. For `m = n - 3` that is every character with a zero
    twist value. On `P_5`, `m = 2`, the criterion gives `Sigma^1` when `d = 1`,
    and nothing when `d >= 2`.
  - The hypothesis is not vacuous. The Aomoto complex was computed over `F_p`
    for two primes, with exact vanishing over `Q`
    (`experiments/pure-braid-bnsr-complements-are-real-res-2026-09-16/`). It has
    `H^{<=n-3} = 0` at random integer points of:
    - on `P_5`: `c_12 = 0`, `c_123 = 0`, `c_1234 = 0`, and the intersections
      `c_12 = c_34 = 0`, `c_12 = c_123 = 0`, `c_12 = c_345 = 0`,
      `c_123 = c_345 = 0`;
    - on `P_6`: `c_12 = 0`, `c_123 = 0`, `c_1234 = 0`, `c_12 = c_34 = 0`,
      `c_12 = c_123 = 0`, `c_123 = c_456 = 0`, `c_12 = c_34 = c_56 = 0`;
    - on `P_7`: `c_12 = 0`.
    The positive controls (one triple, all rows zero on `P_5`, two triples on
    `P_6`) are resonant as expected. So the claim predicts, for example, that a
    generic zero-sum character with `c_12 = 0` is in `Sigma^2(P_5)`.
  - Where the curve complex dies. At a zero vertex of pair type `{1,2}`,
    `Stab(c) = <T_c> x P_{n-1}` by cabling, and the restriction factors through
    a zero-sum character of `P_{n-1}`. By
    `pure-braid-top-bnsr-invariants-are-center-nonvanishing` and Meinert's
    split-epimorphism corollary it is not in `Sigma^{n-3}`. So the
    Meier–Meinert–VanWyk criterion on `C(D_n)` fails at level `n - 3` at every
    such vertex. The splitting was not re-derived in detail.
  - Untried alternatives: the complex with the zero vertices removed (links
    `C(S_{0,n})` are only `(n-5)`-connected); Morse theory with `chi` on a
    Salvetti or Brady-type complex, as in Zaremsky's proof of Proposition 5.6.
- 2026-09-17 (swarm-0917 worker w20-z-last1; experiments in
  `experiments/pure-braid-translated-jump-loci-2026-09-17/`). **`n = 5`, `m = 2`,
  open cones on both twist-hyperplane types, but not the full statement.**
  - **Salvetti Morse method.** This works, and it is the first method in the graph
    that reaches `Sigma^{n-3}` on a twist hyperplane.
    - It is Bestvina–Brady Morse theory on the universal cover of the Salvetti complex
      of the braid arrangement. The heights are `K·(cocycle of chi) + eta`, with an
      integer tie-break `eta` on the 120 chambers.
    - Ascending links at barycentres are antistar joins, and these are 1-connected
      (`antistar_check_n5.log`). So `[chi] ∈ Sigma^2(P_5)` as soon as each of the 120
      posets `Asc(C)` is 1-connected.
    - An annealing search over `eta` (`climb3.py`) finds certificates. An independent
      exact verifier (`verify_cert.py`) checks them.
    - Control: a generic character with all twist values nonzero is VERIFIED
      (`verify_cert_n5_m2_t5gen.log`).
    - `c_12 = 0`: `chi_1 = (0,25,19,-34,-3,27,10,30,24,-98)` is VERIFIED.
    - `c_123 = 0`: `chi_2 = (5,-12,19,-33,7,27,10,30,24,-77)` is VERIFIED.
    - `margin.py` gives explicit sup-norm radii, 0.0149 and 0.0422.
    - Result: `pure-braid-open-zero-twist-cones-lie-in-sigma-two-of-p5` (route
      `pure-braid-zero-twist-cones-p5-salvetti-morse-certificates`). It is
      computer-assisted and unreviewed.
    - Up to `S_5`, the two cones meet every hyperplane `c_A = 0` in a relatively open
      set. They do not cover the non-resonant part of any hyperplane.
  - **Why finitely many certificates cannot finish the job.** The certified set for
    one `eta` is an open polyhedral cone cut out by the lowest-vertex inequalities.
    - Continuation of a generic certificate toward `c_12 = 0` (`continuation.py`,
      `continuation_cont01.log`) follows `a(t) = base + t·dir`, which reaches the
      hyperplane at `t = 0`.
      - The certificate is inherited at `t = 7` and `t = 5`.
      - It gets stuck at `t = 3`, with defects at 4 chambers, and at `t = 2`.
      - The `c_12 = 0` certificate was found instead by annealing directly on the
        hyperplane.
      - So a certified cone is not stable under deformation toward the hyperplane.
    - The non-resonant set is not bounded away from `R^{<=2}` inside the hyperplane.
      So any cover by finitely many certificates must be refined without bound near
      the resonance variety. A uniform, structural choice of `eta` is needed.
  - **Where the certificates break (elastic LP, `lp_elastic.py`).** On `c_12 = 0`,
    every violated lowest-vertex inequality of the relaxed LP lies in a cell with `1`
    and `2` in a common block.
    - Take two chambers related by the swap `(12)` inside such a cell. At `a_12 = 0`
      they get equal `K`-parts, so only `eta` decides between them.
    - The one with the larger `eta` is never lowest in a cell containing both. So in
      the `{1,2}`-cells `Asc(C)` is decided by `eta` alone, and not by `chi`.
    - So the hard part of `Asc(C)` is concentrated in the sub-Salvetti complexes of
      the `{1,2}`-flats.
    - Suggested decomposition: write `Asc(C)` as a join or union of ascending links of
      the restricted arrangement (strands `{1,2}` merged) and of the localized
      arrangement. Then prove the connectivity by induction on `n`. This matches the
      cabling picture `Stab(c) = <T_c> x P_{n-1}` from the 2026-09-16 attempt.
      Untried.
  - **Kohno–Pajitnov positive charts cannot help.**
    `pure-braid-kohno-pajitnov-cones-miss-twist-hyperplanes` (route
    `...-proof`) shows that every positive chart of `M_{0,n+1}` forces `c_S != 0` on
    every boundary divisor. So cones from positive charts never meet a twist
    hyperplane. This rules out the positivity-and-Novikov route to this claim.
  - **No translated-component obstruction was found.** `scan_tori.py` computed
    twisted Betti numbers with rank-1 local systems on 45 translated subtori
    `prod_{A} t = zeta`, including pairs of twist conditions.
    - `P_5`: generically `[0,0,0,6,6]` on all of them (`scan_tori_n5.json`).
    - `P_4`: `[0,0,2,2]` (`scan_tori_n4.json`).
    - So `V^{<=2}(P_5)` has no translated component along the twist tori, and the
      exponential-tangent-cone upper bound for `Sigma^2` does not obstruct the claim.
  - **Comparison.** The Brady-complex attempt of 2026-09-16 and the curve-complex
    criterion fail at twist zeros. The Salvetti Morse function succeeds on open sets
    because `eta` can break the `(12)`-ties chamber by chamber.
  - Status stays OPEN. The missing piece is a uniform `eta`, or an inductive
    connectivity argument for `Asc(C)` near `R^{<=2}`.
- Known outside this range. `m = 1` is Koban–McCammond–Meier with Cohen–Suciu
  (`pure-braid-bns-invariant-is-circle-complement`). For `m >= n - 2` every
  zero-sum character is resonant (Euler characteristic), so the statement is
  vacuous.

Status: OPEN (swarm lane pure-braid-bnsr-complements, 2026-09-16).
