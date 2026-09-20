---
rg: 2
id: free-group-bank-sfts-path-mix-but-are-not-strongly-irreducible
kind: claim
title: On F_2, strong irreducibility of a nearest-neighbour SFT is half-tree mixing, not path mixing, and the bank SFTs without periodic points are path-mixing but not strongly irreducible
distinct_from:
  proper-sft-covers-exclude-finite-orbits-and-sofic-constants: that shows a counterexample domain over a residually finite group has no finite orbit; this tests, on F_2, the candidate SFTs without finite orbits that such a counterexample would need, and finds the natural ones are not strongly irreducible.
  class-n-groups-have-periodic-points-in-measured-sfts: that gives periodic points from invariant measures; the bank SFTs here have neither, and the point is that they still fail strong irreducibility.
  ownership-subshifts-conserve-shell-waste: that rules out strong irreducibility of ownership and arrow shifts by a shell-waste count; this rules it out for bank (conservation-certified) SFTs by an exact half-tree computation, and gives the exact SI test for all nearest-neighbour SFTs on F_2.
artifacts:
  - experiments/si-tree-sft-periodic-2026-09-17/verify_bank.py
  - experiments/si-tree-sft-periodic-2026-09-17/si_exact.py
  - experiments/si-tree-sft-periodic-2026-09-17/treesft.py
  - experiments/si-tree-sft-periodic-2026-09-17/bank_sft.py
  - experiments/si-tree-sft-periodic-2026-09-17/burn_bank.py
  - experiments/si-tree-sft-periodic-2026-09-17/census_exact.py
---

**ESTABLISHED** (elementary lemma plus an exact, replayable finite computation).

**Setting.** `F_2 = <a, b>`. A nearest-neighbour SFT is given by `R_a, R_b ⊆ A × A`:
`x` is a point when `(x_g, x_{ga}) ∈ R_a` and `(x_g, x_{gb}) ∈ R_b` for all `g`. Every `F_2`-SFT is conjugate to one
(higher-block recoding). `E` is the essential alphabet: the largest set in which every symbol has an
`a`-successor, `a`-predecessor, `b`-successor and `b`-predecessor. Every symbol of `E` occurs in a point.

**Lemma (exact SI test).** For `v` entered from its parent by a letter `δ` and a pattern `p` on a finite set `F`
of the half-tree below `v`, let `W_p(v)` be the set of symbols at `v` with which `p` extends over the half-tree.
Call `X` *half-tree mixing* `HM(r)` if `W_p(v) = E` whenever `p` is globally admissible and `d(v, F) ≥ r`.
- `SI(R) ⇒ HM(R)`: take the second pattern to be one symbol at `v`.
- `HM(r) ⇒ SI(2r − 1)`: `W` obeys `W(v) = fix(v) ∩ ⋂_ε Pred_ε(W(vε))`. If `d(F, G) ≥ 2r − 1`, then below every vertex
  `c` one of `p`, `q` sits at distance `≥ r`, so its `W`-set is `E`, and `Pred_ε(E) = E`. By induction
  `W_{p∪q} = W_p ∩ W_q` at every vertex. Rooting at a site of `F` gives `W_{p∪q} = W_p ≠ ∅`.
- *Path mixing* (every reduced word of length `≥ r` carries a walk between any two symbols) is `HM` restricted to
  one-point patterns. It is necessary for SI and, as below, **not sufficient**.
- The families `Family_k[δ]` of `W`-sets of patterns at distance `≥ k` are computed exactly: the least fixpoint
  for `k = 0`, then `Family_{k+1}[δ] = {⋂_ε Pred_ε(W_ε) : W_ε ∈ Family_k[ε]}`. `HM(r)` holds iff
  `Family_r = {E}`. If the sequence repeats before reaching `{E}`, `X` is not SI.

**Bank SFT** (`bank_sft.py`). Symbols `(τ, A, B)`, `τ ∈ {P, N}`, `A, B ∈ [0, K]`.
- `a`-edge `s → t`: `τ(t) = P` and `A(t) = min(A(s)+1, K)`, or `τ(t) = N`, `A(s) ≥ c` and `A(t) = A(s) − c`. `B` is free.
- `b`-edge: the same with `B`, `d`, and the roles of `P`, `N` swapped.
- **No periodic point if `cd > 1`.** On a finite Schreier graph every `a`-cycle has `#P ≥ c#N` (the `A`-bank
  returns) and every `b`-cycle `#N ≥ d#P`. Summing gives `#P ≥ cd#P`, so the graph is empty.
- The same count bounds approximate microstates. So there are no sofic microstates and no invariant measure.
- The **burn-bank** variant (`burn_bank.py`) allows `A(t) ≤ A(s)+1` and `A(t) ≤ A(s) − c` instead. The same count holds.

**Result** (`verify_bank.py 4 2 2`, written from the edge rules without the bitmask library; `si_exact.py`
agrees). For `K = 4` and `c = d = 2`:
- `|E| = 24` of 50 symbols;
- path-mixing constant `r = 8`;
- 383 / 962 / 383 / 962 achievable half-tree `W`-sets for entry letters `a, a⁻¹, b, b⁻¹`;
- `Family_2 = Family_1 ≠ {E}`, so `Family_k = Family_1` for all `k ≥ 1`. It contains singletons: a far pattern
  pins the root symbol at every depth, so `HM` fails at every radius. **Not SI.**

The burn-bank variants are also path-mixing, without periodic points, and not SI:
`K = 4, c = d = 2` (`|E| = 30`) and `K = 4, c = 2, d = 1` (`|E| = 35`).

*Mechanism.* `τ(v)` is certified from below. `τ(v) = N` is forced when `B(vb⁻¹) < d`, and a low bank is forced by a
run of certified `P`s further down, which needs certified `N`s, and so on. The regress can be continued to any depth
before it is closed by fixed symbols.

**Census with the exact test** (`census_exact.py`).
- Random pairs, `n = 3`: 13125 nonempty, 6674 path-mixing, 5206 SI, all with a periodic point.
- Random pairs, `n = 4`: 6074 nonempty, 3315 path-mixing, 1577 SI (`HM` constants 1 to 8), all periodic.
- Random threshold pairs (never periodic), `n = 6`: 1326 nonempty, none even path-mixing.

**Consequences.**
- A path-mixing check does not certify SI on `F_2`. Earlier path-only tests in
  `experiments/si-tree-sft-periodic-2026-09-17/` (`is_si`, `si_defect`, `search.py`, `local_search.py`) test path
  mixing only.
- The natural SI-without-periodic-points candidates on `F_2` die. This is evidence for the Poirier–Salo suspicion
  (arXiv 2401.16774, after Question 6.16) that no SI `F_2`-SFT lacks periodic points. It is not a proof.
- This is the class a counterexample to `proper-sft-domains-admit-no-dual-failures` on `F_2` must come from.

## Attempts

- **2026-09-20, swarm-0917-w22-w22-gs-last1 [census-computation].** Open question left: does `HM` plus
  no-periodic-point contradict the Farkas certificate `(w, φ, ψ)`?
  - The boundary identity for a half-tree of depth `n` is
    `Σ_leaves κ_{ℓ⁻¹}(x_u) − κ_{δ⁻¹}(x_v) = Σ_edges (edge term) < 0`, with
    `κ_a = φ − w`, `κ_{a⁻¹} = −φ`, `κ_b = w − ψ` and `κ_{b⁻¹} = ψ`.
  - Under `HM` this gives only the linear recursion `z_{n+1}(δ) = Σ_{ε ≠ δ⁻¹} z_n(ε)`, which is consistent.
    The certificate alone gives no contradiction.
