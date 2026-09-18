---
rg: 2
id: rover-nekrashevych-polynomial-activity-tower-sigma-full
kind: claim
title: For every contracting self-similar group G of polynomial activity growth, V_{d,r}G has type F_infinity and every BNSR invariant is the whole character sphere
distinct_from:
  rover-nekrashevych-bounded-automata-sigma-invariants-full: that covers bounded automata groups, activity degree 0, with one germ extension over V_{d,r} and characters vanishing on the base; this covers every polynomial degree n through a tower of n+1 germ extensions whose bases carry characters.
  rover-nekrashevych-higher-sigma-invariants-are-full: that asks for Sigma^m(V_d G) = S when G has type F_m, through the Stein–Farley complex; this needs no finiteness of G, only contraction and polynomial activity.
  germ-extension-point-fixer-sigma-heredity: that is the abstract heredity theorem for finite germ extensions; this checks its hypotheses for the Belk–Hyde–Matucci activity tower of Röver–Nekrashevych groups.
---

**ESTABLISHED (proof in `rover-nekrashevych-polynomial-activity-tower-sigma-full-proof`; unreviewed).**

Let `d >= 2`, `r >= 1` and `G <= Aut(T_d)` self-similar. `g|_v` is the section of `g` at `v in X_d^*`.

- `θ_k(g)` is the number of `v in X_d^k` with `g|_v != 1`.
- `g` has *degree `<= i`* when `θ_k(g) = O(k^i)` (for `i >= 0`), and degree `<= −1` when `θ_k(g) = 0` for all large `k`
  (`g` is finitary).
- `G` has *polynomial activity growth* if every element has degree `<= n` for one fixed `n`.
- `G` is *contracting* if there is a finite `N ⊂ G` such that each `g in G` has `g|_v in N` for all `v` of length at
  least some `L(g)`.

These are the definitions in the Belk–Hyde–Matucci remark after `thm:RoverNek` (arXiv:2407.03149).

**Theorem.** Let `G` be contracting with polynomial activity growth, and put `Γ = V_{d,r}G`. Then:

1. `Γ` has type `F_∞`;
2. `Σ^m(Γ) = S(Γ)` for every `m >= 1`;
3. every `N ⊴ Γ` with `Γ/N` abelian has type `F_∞`.

For `r = 1` the sphere `S(Γ)` is the sphere of sum-invariant characters of `G`
(`rover-nekrashevych-characters-are-sum-invariant`). This answers Zaremsky Problem 1.14 for the class.

Item 1 is the claim Belk–Hyde–Matucci sketch in their remark ("from the structure of the automata, one can see …").
The route gives a complete argument.

**How it works.**

- **The tower.** `G_i` is the set of elements of degree `<= i`, and `Γ_i = V_{d,r}G_i`. Then
  `V_{d,r} = Γ_{−1} <= Γ_0 <= ... <= Γ_n = Γ`.
- **Heredity.** `germ-extension-point-fixer-sigma-heredity` carries full `Σ^m` on point-fixers of rational points up
  each step.
- **Hypotheses.** They are checked with elementary tools:
  - a cone-patching lemma;
  - a circuit lemma: polynomial activity forces the automaton's nontrivial circuits to be simple and unchained above
    level `i`. So singular points of `Γ_{i+1}` over `Γ_i` are finitely many, rational, and have tails from the nucleus.
  - a nucleus count of germs at rational points.
- **Base case.** `V_{d,r}` has no characters, and its rational point-fixers have type `F_∞`
  (`higman-thompson-rational-point-fixers-are-f-infinity`).
- **The two kinds of character.**
  - For a character of `Γ_{i+1}` that vanishes on `Γ_i`, the germ-charge Morse theorem applies.
  - For one that does not, Meinert's criterion on `K_{<=m}` applies, and it needs the point-fixers of `Γ_i`. Every
    nonzero character of a Röver–Nekrashevych group is nonzero on every point-fixer (Lemma L of the route). So the
    induction closes.

**Scope and calibration.**

- **`n = 0`.** This recovers `rover-nekrashevych-bounded-automata-sigma-invariants-full` for bounded automata groups,
  with the stronger relative statement `Φ_∞(Γ_0, rational points)`.
- **Not covered.** Self-similar `G` that is not contracting, or has super-polynomial activity. The route uses
  contraction twice: for finitely many tails of singular points, and for finite germ index.
- **Examples of degree `>= 1`.** Contracting groups of activity degree `>= 1` that carry a nonzero sum-invariant
  character are not exhibited here; see Attempts.

## Attempts

- Proved; see the route. The Basilica group and the odometer are degree 0 and were already covered.
