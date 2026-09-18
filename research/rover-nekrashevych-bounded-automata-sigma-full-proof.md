---
rg: 2
id: rover-nekrashevych-bounded-automata-sigma-full-proof
kind: route
title: Check the four hypotheses of the base-trivial germ-extension theorem for V_{d,r}G over V_{d,r}
target: rover-nekrashevych-bounded-automata-sigma-invariants-full
requires:
  - germ-extension-base-trivial-characters-lie-in-sigma
  - germ-complex-and-bux-gonzalez-morse-inputs
  - rover-nekrashevych-characters-are-sum-invariant
---

Let `Γ = V_{d,r}G` with `G` a bounded automata group, and put `B = V_{d,r}`. By item (RN) of
`germ-complex-and-bux-gonzalez-morse-inputs`, `Γ` is a finite germ extension of `B` of type `F_∞`. Fix `m >= 1` and check
hypotheses 1–4 of `germ-extension-base-trivial-characters-lie-in-sigma`.

1. **Finitely many orbits on `sing(Γ)^{m+1}`.** This is item (RN).
2. **`Fix_B(M)` has type `F_m` for `|M| <= m+1`.** Item (RN) gives `Stab_B(M)` of type `F_∞` for every finite
   `M ⊆ sing(Γ)`, and `Fix_B(M)` has finite index in `Stab_B(M)`.
3. **`|(Γ)_p : (B)_p| < ∞`.** This is item (RN).
4. **Infinite `B`-orbits.** Let `p in C_{d,r}` and let `α` be a prefix of `p` with `C_α != C_{d,r}`.
   - The complement of `C_α` contains infinitely many pairwise disjoint cones `C_{β_1}, C_{β_2}, ...`. For example, if
     `C_β` is a cone disjoint from `C_α`, take `β_j = β 1^{j-1} 0`, with `0 != 1` in `X_d`.
   - Every proper cone has a complement that is a finite union of cones. Two disjoint cones `C_α` and `C_{β_j}` can
     therefore be exchanged by an element `t_j in V_{d,r}`: prefix replacement `αw <-> β_j w`, and the identity elsewhere.
   - Write `p = αψ`. Then `t_j(p) = β_j ψ`, and these points are pairwise distinct. So `B·p` is infinite.

**Every character vanishes on `B`.** The Higman–Thompson group `V_{d,r}` has finite abelianization (Higman 1974, at
statement level; for `r = 1` this is also step 5(a) of `rover-nekrashevych-characters-are-sum-invariant-proof`). So
`χ(B) = 0` for every `χ in Hom(Γ, R)`.

**Conclusion.** The theorem gives `[χ] in Σ^m(Γ)` for every nonzero `χ` and every `m`. Hence `Σ^m(Γ) = S(Γ)` for all `m`.

**Normal subgroups.** If `N ⊴ Γ` and `Γ/N` is abelian, every character vanishing on `N` lies in `Σ^m(Γ)`. By
Bieri–Renz (`rover-nekrashevych-higher-sigma-full-via-kernel-brown`, item (BR)), `N` has type `F_m` for every `m`. ∎

**Examples.**

- The binary odometer `a = σ(1,a)` is a bounded automata group: its sections are nontrivial only along `1^∞`. It has
  `Hom(V_2(Z), R) = R` (`rover-nekrashevych-characters-are-sum-invariant`).
- Belk–Hyde–Matucci list the Basilica group as a bounded automata group. Its section map exchanges `a` and `b`, so the
  sum-invariant characters are `χ(a) = χ(b)`.
