---
rg: 2
id: rover-nekrashevych-bounded-automata-sigma-invariants-full
kind: claim
title: For every bounded automata group G, all BNSR invariants of the Rover--Nekrashevych groups V_{d,r}G are the whole character sphere
distinct_from:
  rover-nekrashevych-higher-sigma-invariants-are-full: that asks for Sigma^m(V_d G) = S when G has type F_m, via the Stein–Farley complex; this proves Sigma^infinity(V_{d,r}G) = S for bounded automata G through the germ complex, including groups such as the Basilica group that are not finitely presented.
  rover-nekrashevych-groups-have-full-bns-invariant: that proves Sigma^1 = S for every finitely generated self-similar G; this proves every Sigma^m = S, but only for bounded automata G.
---

**ESTABLISHED (proof in `rover-nekrashevych-bounded-automata-sigma-full-proof`; unreviewed).** Let `d >= 2`, `r >= 1`,
and let `G <= Aut(T_d)` be a bounded automata group. Put `Γ = V_{d,r}G`. Then:

- `Σ^m(Γ) = S(Γ)` for every `m >= 1`, that is `Σ^∞(Γ) = S(Γ)`;
- every normal subgroup `N` of `Γ` with `Γ/N` abelian has type `F_∞`.

This answers Zaremsky Problem 1.14 for the class of bounded automata groups. By
`rover-nekrashevych-characters-are-sum-invariant`, for `r = 1` the sphere `S(Γ)` is the sphere of sum-invariant
characters of `G`.

**Where it has content.**

- **Binary odometer** `a = σ(1,a)`: `S(V_2(Z)) = S^0`, and both kernels of `V_2(Z) -> Z` have type `F_∞`.
- **Basilica group.** Assuming its abelianization is `Z^2` (Grigorchuk–Żuk, not re-derived), the sum-invariant
  characters are `χ(a) = χ(b)`. So `S(V_2(Basilica)) = S^0` and `Σ^∞ = S^0`. This settles the first test named in
  `rover-nekrashevych-bnsr-invariants-are-full`, where the Stein–Farley route fails because Basilica is not finitely
  presented.
- For torsion `G` (Grigorchuk, Gupta–Sidki) the sphere is empty and the statement is vacuous.

## Attempts

- Proved from `germ-extension-base-trivial-characters-lie-in-sigma` applied to `B = V_{d,r}` for every `m`.
- **Next class.** Contracting `G` with polynomial activity growth. Belk–Hyde–Matucci pass from `V_{d,r}G_i` to
  `V_{d,r}G_{i+1}` by a finite germ extension whose base `V_{d,r}G_i` can carry characters, so the base-trivial theorem
  does not apply directly.
