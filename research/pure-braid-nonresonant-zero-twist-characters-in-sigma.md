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
- Known outside this range. `m = 1` is Koban–McCammond–Meier with Cohen–Suciu
  (`pure-braid-bns-invariant-is-circle-complement`). For `m >= n - 2` every
  zero-sum character is resonant (Euler characteristic), so the statement is
  vacuous.

Status: OPEN (swarm lane pure-braid-bnsr-complements, 2026-09-16).
