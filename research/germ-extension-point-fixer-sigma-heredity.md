---
rg: 2
id: germ-extension-point-fixer-sigma-heredity
kind: claim
title: Full Sigma^m on point-fixers passes from the base to a finite germ extension whose point-fixers are again finite germ extensions
distinct_from:
  germ-extension-base-trivial-characters-lie-in-sigma: that proves Sigma^m for characters vanishing on the base, with the base-orbits infinite; this proves an inductive statement for all characters, on all point-fixers, and allows fixed singular points.
  germ-extension-base-nontrivial-characters-via-point-fixers: that is one step (characters nonzero on the base) for a single group; this combines both cases and makes the hypothesis on point-fixers hereditary, so it can be iterated along a tower.
---

**ESTABLISHED (proof in `germ-extension-point-fixer-sigma-heredity-proof`; unreviewed).**

Let `B <= G <= Homeo(X)` with `X` Hausdorff, and let `P ⊆ X`. For a finite `M ⊆ X` write `G_M = Fix_G(M)` and
`B_M = Fix_B(M)`. For a group `A <= Homeo(X)` and `m >= 1`, let `Φ_m(A,P)` be the statement:

> for every finite `M ⊆ P`, `A_M` has type `F_m`, and `[ψ|_{A_M}] in Σ^m(A_M)` for every `ψ in Hom(A,R)` with `ψ|_{A_M} != 0`.

Say that `A` *localizes over `P`* if every nonzero `ψ in Hom(A,R)` is nonzero on `A_M` for every finite `M ⊆ P`.

**Theorem.** Fix `m >= 1`. Assume that `B` and `G` localize over `P`, and that for every finite `M ⊆ P`:

- (H1) `G_M` is a finite germ extension of `B_M`, and `sing(G_M) ⊆ P`;
- (H2) `B_M` has finitely many orbits on `sing(G_M)^{m+1}`;
- (H3) `|(G_M)_p : (B_M)_p| < ∞` for every `p in sing(G_M)`;
- (H4) every `B_M`-orbit in `sing(G_M)` is either infinite or a whole `G_M`-orbit.

Then `Φ_m(B,P)` implies `Φ_m(G,P)`.

**Corollary (towers).** Let `B_0 <= B_1 <= ... <= B_n <= Homeo(X)`. Suppose each pair `B_i <= B_{i+1}` satisfies the
hypotheses of the theorem for every `m`, and `Φ_m(B_0,P)` holds for every `m`. Then `Φ_m(B_n,P)` holds for every `m`.
With `M = ∅`: `B_n` has type `F_∞` and `Σ^∞(B_n) = S(B_n)`. By Bieri–Renz (item (BR) of
`rover-nekrashevych-higher-sigma-full-via-kernel-brown`), every `N ⊴ B_n` with `B_n/N` abelian has type `F_∞`.

**How it works.** Fix `M` and a nonzero `χ in Hom(G,R)`, and put `ψ = χ|_B`.

- If `ψ = 0`, then `χ` vanishes on `B_M` and is nonzero on `G_M`. The germ-charge Morse theorem applies to
  `G_M ⊇ B_M`. Its hypothesis 4 (infinite base orbits) is weakened to (H4), which allows points of `M` that are fixed
  singular points.
- If `ψ != 0`, then `ψ` is nonzero on every `B_{M ∪ M'}`. `Φ_m(B,P)` puts it in `Σ^m`, and
  `germ-extension-base-nontrivial-characters-via-point-fixers` applies to `G_M ⊇ B_M`. Its point-fixers are
  `Fix_{B_M}(M') = B_{M ∪ M'}`.

The hypothesis `Φ_m` is about point-fixers because the base-nontrivial step needs exactly the point-fixers of the base.
This is what makes the statement iterate.

## Attempts

- Proved; see the proof route. Applied to the polynomial-activity tower in
  `rover-nekrashevych-polynomial-activity-tower-sigma-full`.
