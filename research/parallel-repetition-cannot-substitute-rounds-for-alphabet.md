---
rg: 2
id: parallel-repetition-cannot-substitute-rounds-for-alphabet
kind: claim
title: Unless P = NP, every route that outputs the l-fold repetition G^l of polynomial-time computed bipartite unique games of alphabet k has sqrt-scale deficit ratio at most 2 C_1 sqrt(ln k) for every l and every soundness analysis, and per-round rate at most 7.51 C_1^2 eta ln k on hard sources, so sqrt-scale UG hardness at ratio C or UGC at eps by repetition needs a base alphabet exp(C^2/4C_1^2) or exp(1/16 C_1^2 eps), and rounds never pay for alphabet
distinct_from:
  sqrt-scale-ug-hardness-costs-alphabet-exp-c-squared: that prices the OUTPUT alphabet by CMM, log(k^l) = l log k >= C^2/4A^2, which rounds can pay for, and it concludes NP in RP. This prices the BASE alphabet, log k >= C^2/4C_1^2, uniformly in l, and it concludes P = NP, because it needs only the base SDP value and no rounding.
  expansion-certified-repetition-caps-deficit-ratio: that kills repetition routes whose soundness is CERTIFIED by rates of the shape K gamma^2 + kappa lambda gamma, and leaves the survivor (P2). This bounds the TRUE value of G^l on every NO output, with no hypothesis on how soundness is argued or on expansion, and prices (P2) in base alphabet.
  black-box-repetition-needs-sqrt-scale-soundness-gap: that kills universal repetition bounds via the odd cycle, with no complexity assumption; this kills every repetition route whose base alphabet is below exp(C^2/4C_1^2), whatever bound is used, conditional on P != NP.
  steurer-parallel-repeated-unique-games-rounding: that is the imported rounding theorem; this is its consequence for NP-hardness routes, through the polynomial-time computability of the base SDP.
  sqrt-scale-unique-games-hardness: that is the open hole; this kills one class of routes to it (bounded-alphabet repetition) and sharpens the (P2) survivor into two independently failing prerequisites.
  parallel-repetition-collapses-threshold-rank-to-spectral-gap: that tracks the output spectrum of a repetition; this bounds the output value by the base SDP.
artifacts:
  - experiments/ugc-repetition-alphabet-ceiling-2026-09-17/check_repetition_alphabet_ceiling.py
  - experiments/ugc-repetition-alphabet-ceiling-2026-09-17/output.txt
---

**ESTABLISHED (class kill, conditional on P != NP only through its conclusion).**
Proof: `parallel-repetition-cannot-substitute-rounds-for-alphabet-proof`.

## Setting

- **Games.** Unique games are bipartite, with rational weights, as in
  `sqrt-scale-unique-games-hardness`. `opt` is the value and `sdp` is the basic
  SDP value (norm-sum-one and orthogonality constraints), as in
  `steurer-parallel-repeated-unique-games-rounding`. `C_1 >= 1` is the absolute
  constant of (S1) there, and `ln` is the natural logarithm.
- **Repetition route.** A repetition route is a polynomial-time map `x ↦ G_x`
  onto bipartite unique games with alphabet `[k]`, `k >= 2`, together with a
  positive integer `l` whose bit size is polynomial. Nothing else bounds `l`.
  The route outputs `H_x = G_x^l`, whose alphabet is `k^l`.
- **Promise problem.** The route's promise problem is `Pi = (Y, N)`.

## Statements

**Theorem RA.**

- **(a) Product completeness; uses (S1) only.** Suppose that
  `x in Y ⇒ opt(G_x) >= 1 − η` and that `x in N ⇒ opt(G_x^l) <= 1 − Γ`, with
  `η` rational and `Γ > C_1 sqrt(1.5 l η ln k)`. Then `Pi` is in `P`.
- **(b) General completeness; uses (S1) and (S2).** Suppose that
  `x in Y ⇒ opt(G_x^l) >= 1 − η_out` with rational `η_out <= 1/2`, that
  `x in N ⇒ opt(G_x^l) <= 1 − Γ`, and that `Γ > C_1 sqrt(3 η_out ln k)`. Then
  `Pi` is in `P`.
- **(c) Ratio ceiling.** Let `η_out` be the output completeness deficit, with
  `η_out := 1 − (1 − η)^l` in case (a), and assume `η_out <= 1/2`. Then, unless
  `Pi` is in `P`,

  ```text
  C_out := Γ / sqrt(η_out)  <=  2 C_1 sqrt(ln k)        for every l >= 1.
  ```

**Corollary RA (unless P = NP).**

1. **Sqrt scale.** Suppose a repetition route makes
   `Gap-UG_{k^l}[1 − η_out, 1 − C sqrt(η_out)]` NP-hard. Then
   `ln k >= C^2/(4 C_1^2)`. This holds for every `l`.
2. **UGC.** Suppose a repetition route makes `Gap-UG_{k^l}[1 − ε, ε]` NP-hard,
   with `ε <= 1/2`. Then `ln k >= (1 − ε)^2/(4 C_1^2 ε) >= 1/(16 C_1^2 ε)`.
3. **Rate ceiling.** This part is unconditional. Let `G` be any bipartite
   unique game with alphabet `k`. Suppose that `opt(G^l) <= (1 − ψ)^l` at
   `l = ⌈1/ψ⌉`, where `ψ in (0,1]`. Then
   `ψ <= 5.01 C_1^2 (1 − sdp(G)) ln k`.
4. **Hard sources.** Let `Gap-UG_k[1 − η, 1 − γ]` be NP-hard, with any extra
   promise on its NO instances (for example, λ-gapped). Then it has a NO
   instance with `sdp >= 1 − 1.5η`. Any per-round rate `ψ` valid on all its NO
   instances therefore satisfies `ψ <= 7.51 C_1^2 η ln k`.

## Class kill (impact type 3)

- **Invariant.** The invariant is the base SDP deficit `1 − sdp(G)`. Under
  repetition it grows at most `l`-fold, by (S2). Under rounding it costs only
  `sqrt(l · deficit · ln k)` in the value of `G^l`, with the base alphabet, not
  `ln(k^l)`, by (S1).
- **Where every member dies.** Members die at the soundness of the output.
  - A NO output with `opt(G^l) <= 1 − Γ` and `Γ > 2 C_1 sqrt(η_out ln k)`
    forces `sdp(G) < 1 − 1.5 η` at the base.
  - YES forces `sdp(G) >= 1 − η` at the base.
  - The base SDP, computed on `G_x` rather than on the exponentially larger
    `G_x^l`, then decides `Pi`.
- **What is killed.** Every route to `sqrt-scale-unique-games-hardness` or to
  UGC of the form "NP-hard base family, then `G ↦ G^l`" with
  `ln k < C^2/(4C_1^2)` (respectively `ln k < (1−ε)^2/(4C_1^2 ε)`). This holds
  for any number of rounds and any soundness argument:
  - universal bounds (Raz, Holenstein, Rao, Dinur–Steurer);
  - expansion bounds (AKKSTV, Raz–Rosen);
  - small-set-expansion bounds (the withdrawn Moshkovitz arXiv 2103.08743);
  - threshold rank;
  - no argument at all.

  In particular, every fixed-alphabet base (Max-Cut, 2-LIN, or any bounded `k`)
  with growing `l` is capped at `C_out <= 2 C_1 sqrt(ln k)`. The case `k = 2` at
  UGC scale is the Barak–Hardt–Haviv–Rao–Regev–Steurer conclusion. This claim
  extends it to every base alphabet, to the sqrt scale, and to arbitrary
  completeness.
- **Where the survivor (P2) now sits.** The survivor of
  `expansion-certified-repetition-caps-deficit-ratio` must meet two
  prerequisites, each of which can fail on its own:
  - **(R1)** An NP-hard base `Gap-UG_k[1 − η, 1 − γ]` whose NO instances are
    λ-gapped, at alphabet `ln k >= C^2/(4 C_1^2)`.
  - **(R2)** A rate `ψ`, valid on that base's NO instances (the SDP-fooling ones
    of item 4 included), in the window

    ```text
    0.79 C  <=  ψ/η  <=  7.51 C_1^2 ln k .
    ```

    The lower end is what a rate-certified route needs to output ratio `C`.
    The upper end is item 4.

  Rates superlinear in `λγ` must therefore be paid for by base alphabet. They
  cannot be supplied by rounds.

## Checks

`experiments/ugc-repetition-alphabet-ceiling-2026-09-17/check_repetition_alphabet_ceiling.py`
writes `output.txt` and ends in ALL PASS. It checks:

- the elementary inequalities of the proof, numerically on grids:
  - `(1 − x)^(1/l) >= 1 − 2x/l` on `(0, 1/2]`;
  - `lη <= 2η_out`;
  - `η_out >= (1 − 1/e) lη`;
  - the rate constant `2/(1 − 1/e)^2 <= 5.01`;
- on the odd-cycle game (`k = 2`, which is Raz's and the tight family), an
  explicit feasible basic-SDP solution: constraints to `1e-12`, and deficit
  `sin^2(π/4m)`;
- brute-force `opt(G)` and `opt(G^2)` at small `m`;
- that `(1 − opt(G^l))/sqrt(l · sdp-deficit · ln 2)` stays bounded. This is the
  shape of (S1), and it is illustrative, not a proof of the constant.

## What is not covered (survivors)

- **Heterogeneous products `G_1 × ... × G_l`.** (S1) is imported only for
  `G^l`. Extending it to products needs Lemma 9 and Theorem 3 of Steurer in
  product form, which is unchecked.
- **Derandomized or partial repetition.** Examples are sampling `l`-tuples by
  expander walks, and fortification.
- **Repetition followed by alphabet reduction or composition.** An inner PCP is
  applied after `G ↦ G^l`, so the final output is no longer a repetition.
- **Routes whose base alphabet already satisfies `ln k >= C^2/(4C_1^2)`.**
