---
rg: 2
id: jz-question-5-for-thompson-t-implies-f-nonamenable
kind: claim
title: Thompson's T factors exactly as F times the dyadic rotations, so if F is amenable then T acting on the cosets of the rotations is a finitely presented counterexample to Juschenko–Zheng's Question 5, and a positive answer to Question 5 for T alone proves F nonamenable
distinct_from:
  juschenko-zheng-question-5-fails-for-countable-groups: that refutes Question 5 unconditionally for the non-finitely-generated group SL_2(R_alg) via G = BK; this is the same mechanism for the finitely presented group T via T = F·R_D, conditional on amenability of F, and turned around it constrains the root.
  liouville-action-criteria-cannot-decide-thompson-f-amenability: that kills Liouville-action criteria except the survivor "Question 5 for finitely generated groups plus an abelian-stabilizer Liouville F-set"; this kills that survivor, since Question 5 for finitely generated groups (even for T alone) already implies F is nonamenable.
  amenably-coupled-actions-admit-symmetric-liouville-measures: that is the LAT criterion (Theorem A), used here as a black box; this supplies the exact factorization of T and the resulting implication between the root and Question 5.
  thompson-f-is-not-amenable: that is the open non-amenability claim; this proves it from a positive answer to Question 5 for T, a hypothesis Juschenko and Zheng expect to be false.
  thompson-f-not-amenable-iff-thompson-t-cstar-simple: that is another statement about T equivalent to or implying non-amenability of F; this one goes through random walks on T/R_D rather than reduced C*-algebras.
---

**ESTABLISHED** through `jz-question-5-for-thompson-t-implies-f-nonamenable-proof`. The root
`thompson-f-is-amenable` stays OPEN.

**Notation.** `T` acts on `S¹ = R/Z`; `D/Z` is the set of dyadic points; `F = Stab_T(0)`; for `θ ∈ D/Z`,
`ρ_θ(t) = t + θ`; `R_D = {ρ_θ : θ ∈ D/Z} ≅ Z[1/2]/Z`, the Prüfer 2-group (abelian, locally finite).
Question 5 (Q5) is as quoted in `juschenko-zheng-liouville-actions`.

**Theorem.**
1. *(Exact factorization.)* `T = F·R_D` and `F ∩ R_D = 1`. Every `g ∈ T` is uniquely `g = f ρ` with
   `f ∈ F`, `ρ ∈ R_D`; explicitly `ρ = ρ_{-g^{-1}(0)}` and `f = g ρ_{g^{-1}(0)}`.
2. *(The T-set.)* `X = T/R_D` is a transitive `T`-set whose point stabilizers are the conjugates of `R_D`,
   hence abelian and locally finite. `F` acts on `X` simply transitively, so `X ≅ F` as an `F`-set.
3. *(Conditional counterexample.)* If `F` is amenable, then `T ↷ X` is locally amenably transitive, so for
   every generating sequence of `T` there is a symmetric `µ` on `T` containing it in its support with
   `(X, P_µ)` Liouville. Since `T` is finitely presented and nonamenable, `(T, X, µ)` answers Q5 negatively
   for a finitely presented group, with non-degenerate symmetric `µ` and locally finite abelian stabilizers.
4. *(Contrapositive.)* If Q5 has a positive answer for the single group `T` (even only for symmetric
   non-degenerate `µ` and locally finite abelian stabilizers), then `F` is not amenable.

**What this kills.** The last survivor of `liouville-action-criteria-cannot-decide-thompson-f-amenability`:
"apply Q5 for finitely generated groups to a Liouville `F`-set with abelian stabilizers to get amenability".
- *Invariant.* The exact factorization `T = F·R_D` with `R_D` abelian.
- *Dying step.* "Assume Q5 for finitely generated groups". Applied to `T`, which is finitely generated, it
  already yields that `F` is nonamenable (item 4). So the route's hypothesis contradicts its conclusion. No
  consistent use of Q5, or of any "Liouville + stabilizers in class `𝒮` ⟹ amenable" criterion for finitely
  generated groups with `𝒮` containing the Prüfer 2-group, can prove the root.
- The amenable-stabilizer variant dies even more directly: `T ↷ D/Z` is Liouville unconditionally
  (`amenably-coupled-actions-admit-symmetric-liouville-measures`, Corollary 3) with stabilizer `F`, so
  "Liouville + amenable stabilizers ⟹ amenable" for finitely generated groups would itself make `F`
  nonamenable.

**Belief change.** `thompson-f-is-amenable` now implies that Q5 fails for finitely generated groups, which
Juschenko and Zheng expect ("these questions should have a negative answer"). So amenability of `F` is
consistent with their expectation, and a positive answer to their Question 5 for `T` would settle the root
negatively. Any proof of `thompson-f-is-amenable` must also produce a finitely presented Q5 counterexample.

**Where the next hole is.** Whether `T ↷ T/R_D` is LAT without assuming the root is
`thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive` (OPEN), which would prove `F` nonamenable;
its negation would answer Q5 negatively for finitely generated groups outright.
