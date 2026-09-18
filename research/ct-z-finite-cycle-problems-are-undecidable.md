---
rg: 2
id: ct-z-finite-cycle-problems-are-undecidable
kind: claim
title: In Kohl's class transposition group CT(Z) it is undecidable whether a given element has only finite cycles, and whether it has no finite cycles; this answers Kourovka Problem 21.74(b) and (c) negatively
requires:
  - ct-z-north-south-element-has-no-finite-cycles
artifacts:
  - research/artifacts/gq-bh-bh-free-58-kari-ollinger-source.md
---

**ESTABLISHED** (lane proof, not reviewed).

- **Inputs.**
  - Kari–Ollinger, MFCS 2008, Theorems 3 and 6, read at source (see the artifact). They
    are published, but the paper gives proof sketches only.
  - The elementary node `ct-z-north-south-element-has-no-finite-cycles`.
- **Membership in CT(Z)** comes from explicit words in class transpositions. It does
  not use `ct-p-z-is-a-one-vertex-k-graph-full-group` or 17.59.
- **Priority.** None is claimed. An arXiv search (class transposition,
  residue-class-wise) found no paper on 21.73 or 21.74. The 21st issue (2026) lists
  both as unsolved.
- **Not settled here.** Part (a) of 21.74, and 21.73.

## Statement

Kourovka 21.74 (S. Kohl) asks whether it is decidable, for a given `g ∈ CT(Z)`,
whether `g`
- (a) permutes a nontrivial partition of `Z` into residue classes;
- (b) has only finite cycles;
- (c) has no finite cycles.

**Theorem.** An algorithm takes a reversible 2-counter machine `M` and outputs words
`F_M` and `H_M` in class transpositions. All moduli in these words are
`{2,3,5,7,11,13}`-smooth, and:

1. `F_M` has only finite cycles on `Z` iff every configuration of `M` is periodic.
2. `H_M` has no finite cycle on `Z` iff `M` has no periodic configuration.

Combined with Kari–Ollinger:
- Theorem 3 (periodicity of complete 2-RCM is undecidable) makes (b) undecidable.
- Theorem 6 (it is undecidable whether a 2-RCM admits a periodic configuration) makes
  (c) undecidable.

Both hold already in `CT_P(Z)` with `P = {3,5,7,11,13}`. They hold whether `g` is given
as a word or as an rcwa map, because the rcwa table of a word is computable.

## The machine (Kari–Ollinger conventions)

- **Machine.** `M = (S, 2, T)` with `S = {1, …, N}`. An instruction `(s, u, i, φ, t)`
  applies to a configuration `(s, v)` whose zero/positive pattern is `u`, and changes
  counter `i` by `φ ∈ {−1, 0, +1}`. `M` is deterministic, `G` is its partial
  transition map, and the reversed table `T^{-1}` is deterministic too.
- **(R1) `G` is injective.** Suppose `G(x) = G(x') = y` by instructions `ι` and `ι'`.
  - Some reversed instruction of `ι` applies at `y`, and one of `ι'` does too. For
    `φ = −` the reverse of `ι` consists of two instructions, and the zero pattern of
    `y` picks one.
  - Both have source state and test vector equal to those of `y`. Since `T^{-1}` is
    deterministic, they have the same action and target.
  - Each maps `y` back to `x` (resp. `x'`), so `x = x'`.
- **(R2) Two finite unions of cells.**
  - `Halt = {x : G(x) undefined}`.
  - `Init = {y : y ∉ G(S × N^2)}`.
  - Both are finite unions of *cells*: a state together with, for each counter, whether
    it is `0`, `1` or `≥ 2`.
  - Reason: an instruction `(s, u, i, φ, t)` maps its domain onto the set of `(t, w)`
    with `w_j` in the class of `u_j` (zero or positive) for `j ≠ i`. The condition on
    `w_i` is:
    - the class of `u_i`, if `φ = 0`;
    - `w_i = 1` or `w_i ≥ 2`, according to `u_i`, if `φ = +`;
    - none, if `φ = −`.

## The element

For `n ≠ 0` let `e_p(n)` be its `p`-adic valuation. We consider `n` with `e_2(n) = 0`
and `1 ≤ e_7(n) ≤ N`.

- **Codes.** Such an `n` is:
  - a *configuration code* if `e_11 = e_13 = 0`; its configuration is
    `c(n) = (e_7, (e_3, e_5))`;
  - a *backward-ray code* if `e_11 ≥ 1`, `e_13 = 0` and `c(n/11^{e_11}) ∈ Init`;
  - a *forward-ray code* if `e_13 ≥ 1`, `e_11 = 0` and `c(n/13^{e_13}) ∈ Halt`.
- **The map.** Let `X` be the set of codes, and define `f : X → X` by:
  - `f(n) = 7^{t−s} 3^{φ_1} 5^{φ_2} n` on configuration codes with `c(n) ∉ Halt`, where
    the applicable instruction goes to state `t` and changes the counters by
    `(φ_1, φ_2)`;
  - `f(n) = 13n` on configuration codes with `c(n) ∈ Halt`, and on forward-ray codes;
  - `f(n) = n/11` on backward-ray codes.

**Claim 1.** `f` is a bijection of `X`, and its finite cycles are exactly the codes of
periodic configurations.

- Write `n = ±w·∏ p^{e_p}` with `w` prime to 2·3·5·7·11·13. Then `f` preserves the sign
  and `w`.
- Fix the sign and `w`. Then `f` acts as follows:
  - as `G` from `Conf ∖ Halt` onto `Conf ∖ Init`, bijectively by (R1);
  - as `j ↦ j+1` on the exponent of 13, from `Halt ∪` forward rays onto forward rays;
  - as `j ↦ j−1` on the exponent of 11, from backward rays onto backward rays `∪ Init`.
- These three domains partition `X`, and so do the three images.
- Along backward-ray codes the exponent of 11 strictly decreases, and only
  backward-ray codes map to backward-ray codes. Forward rays are never left. Hence a
  finite cycle consists of configuration codes, on which `f = G`. ∎

**Claim 2.** Put `L = 2·3²·5²·7^{N+1}·11·13`.
- `X`, and the domain of each formula above, are unions of classes mod `L`. Membership
  reads only `e_2 ∈ {0, ≥1}`, `e_3, e_5 ∈ {0, 1, ≥2}`, `e_7 ∈ {0, …, N, ≥N+1}` and
  `e_11, e_13 ∈ {0, ≥1}`.
- On each class `c(L) ⊆ X` with `0 ≤ c < L`, `f(n) = λ_c n` with `λ_c > 0`. Each
  denominator of `λ_c` divides `n`, hence `c`, because it divides `L`.
- So `f` maps `c(L)` canonically onto the class `(λ_c c)(λ_c L)`, via
  `c + Lk ↦ λ_c c + λ_c L k`. ∎

**The word `F_M`.** Let `K = {c : c(L) ⊆ X}` and put

    s_1 = ∏_{c∈K} τ_{c(L), 2c(2L)},    s_2 = ∏_{c∈K} τ_{2c(2L), (λ_c c)(λ_c L)},    F_M = s_2 s_1.

- **Disjointness.** The classes `c(L)` are odd, so they are disjoint from the classes
  `2c(2L)`, which have `e_2 = 1`. The classes `2c(2L)` are pairwise disjoint. The
  classes `(λ_c c)(λ_c L) = f(c(L))` are pairwise disjoint and partition `X`.
- **The two involutions.** So `s_1` and `s_2` are products of class transpositions with
  disjoint supports. `s_1` is `n ↔ 2n` and `s_2` is `2n ↔ f(n)`, for `n ∈ X`.
- **The composite.** `F_M = f` on `X`, `F_M(2n) = 2f^{-1}(n)` on `2X`, and `F_M` is the
  identity elsewhere. Its cycles are those of `f`, copies of those of `f^{-1}`, and
  fixed points.
- **Proof of 1.** If every configuration is periodic, then `Halt = Init = ∅`, so `X`
  consists of configuration codes and `f = G` has finite orbits. Otherwise a
  non-periodic configuration has an infinite `f`-orbit, by Claim 1.

**The word `H_M`.** Put `L' = 4L`.
- `Y = Z ∖ (X ∪ 2X)` is a union of classes `j(L')`.
- For each such class, let `ψ_j` be the five-transposition conjugate of `ψ` supported
  on `j(L')`, as in item 3 of `ct-z-north-south-element-has-no-finite-cycles`. It has
  no finite cycles on `j(L')`.
- Put `H_M = (∏_j ψ_j) F_M`.
- **Proof of 2.** On `X ∪ 2X`, `H_M = F_M`, and `Y` has no finite cycles. So `H_M` has
  no finite cycle iff `f` has none, i.e. (Claim 1) iff `M` has no periodic
  configuration.

**Computability.** Every modulus used is `{2,3,5,7,11,13}`-smooth. `Halt`, `Init`, `K`,
the `λ_c` and `Y` are all computed from `T` by finite checks mod `L'`. ∎

## Remarks

- **More counters.** Any number of counters works, using one prime per counter.
- **Finite order.** `F_M` has finite order iff `M` is uniformly periodic, which is
  decidable (Kari–Ollinger Thm. 4). So this construction says nothing about the
  torsion problem in CT(Z).
- **21.74(a).** Its yes-instances are recursively enumerable:
  - enumerate the partitions `𝒫`;
  - compute `g(C)` for each `C ∈ 𝒫` and test that it is a class of `𝒫`.

  `ψ` is an explicit no-instance. Every product of multiplicative class maps with odd
  multipliers preserves parity, and so is a yes-instance. Decidability remains open
  here.
- **21.73** (conjugacy) remains open here.
