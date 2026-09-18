---
rg: 2
id: liouville-action-criteria-cannot-decide-thompson-f-amenability
kind: claim
title: Liouville measures for actions cannot decide the amenability of Thompson's F, because every locally amenably transitive action is Liouville and any action that is not already certifies nonamenability
distinct_from:
  thompson-f-random-walks-are-not-liouville: that kills finitely supported measures at the group level; this kills the action-level criterion for all measures, both directions.
  thompson-f-finite-entropy-walks-are-not-liouville: that is the open group-level finite-entropy rung; this concerns Liouville measures for actions, which are never decisive, and leaves the group-level question untouched.
  thompson-f-dyadic-orbit-walks-are-transient: that kills recurrence of orbit walks; this kills the Liouville property of orbit walks as a tool, since it always holds for some symmetric measure.
  pl-ea-calibrators-are-nonamenable-interval-groups: that calibrates extensive amenability against PL worlds; this uses Thompson's T from it as a Liouville-but-nonamenable calibrator.
  amenably-coupled-actions-admit-symmetric-liouville-measures: that is the positive Liouville criterion; this is the class kill for the amenability root drawn from it.
---

**ESTABLISHED** through `liouville-action-criteria-cannot-decide-f-proof`. The root
`thompson-f-is-amenable` stays OPEN.

**The class.** Arguments for or against amenability of `F` that pass through Liouville measures of actions
(`juschenko-zheng-liouville-actions`).
- *(N) Negative, Kaimanovich's criterion.* Prove `F` nonamenable by exhibiting an action of `F`, or of a group
  that is amenable whenever `F` is (such as a lamplighter `P_f(X) ⋊ F`), with no non-degenerate Liouville
  measure.
- *(P) Positive.* Deduce amenability of `F`, or extensive amenability of `F ↷ D`, or amenability of some action,
  from the existence of a Liouville measure for an action, possibly with a condition on stabilizers.

**Invariant.** Local amenable transitivity (LAT): every finite set of points lies in one orbit of an amenable
subgroup (`amenably-coupled-actions-admit-symmetric-liouville-measures`).

**Theorem.**
1. *(N) dies on every LAT action.* Every LAT action of a countable group has a non-degenerate symmetric
   Liouville measure. For `F` the LAT actions include:
   - every orbit of `F` in `(0,1)`, including the dyadic orbit, where Kaimanovich's finitely supported theorem
     lives;
   - every transitive `F`-set `F/K` with `F = HK` for an amenable `H`, for instance every `K ⊇ [F,F]`;
   - every lamplighter action `P_f(X) ⋊ F ↷ P_f(X)`, for every transitive `F`-set `X`.
2. *(N) is never decisive off LAT.* If `F` is amenable, every `F`-set is LAT (`H = F`). So an `F`-set that is
   not LAT is already a certificate that `F` is nonamenable. By item 1, a proof that some action has no
   non-degenerate Liouville measure proves in particular that the action is not LAT. The criterion therefore adds nothing beyond the
   elementary *local nonamenability* statement: there is a finite `Y ⊆ X` such that every subgroup of `F` that
   puts `Y` into one orbit is nonamenable.
   - For the regular action, `Y = {e, x_0, x_1}` forces `H = F`, so not-LAT, non-Liouville and nonamenability
     of `F` are one statement (Kaimanovich–Vershik).
3. *(P) dies at "Liouville implies amenable".* A non-degenerate symmetric Liouville measure implies neither
   amenability nor extensive amenability of the action, nor amenability of the group, even for LAT actions with
   cyclic or abelian coupling:
   - `T ↷ D/Z` is finitely generated, locally cyclically transitive and Liouville, yet neither amenable nor
     extensively amenable;
   - `P_f(F_2) ⋊ F_2 ↷ P_f(F_2)` is Liouville and not amenable;
   - `SL_2(R_alg) ↷ SL_2(R_alg)/SO_2(R_alg)` has abelian stabilizers and is Liouville, and the group is not
     amenable (`juschenko-zheng-question-5-fails-for-countable-groups`).

   For `F` itself, `F ↷ D` and `P_f(D) ⋊ F ↷ P_f(D)` are Liouville unconditionally. Yet their extensive
   amenability, respectively their amenability, is equivalent to the root. So a Liouville measure for either
   carries no information about the root.

**Dying step.** For (N), the step "exhibit the action". Any candidate is either LAT, and then Liouville by
Theorem A, or not LAT, and then already a nonamenability certificate without any boundary theory. For (P), the
step "Liouville ⟹ amenable", refuted by the three calibrators.

**Survivors, open.**
- The group-level Liouville program, which is the root itself (`thompson-f-finite-entropy-walks-are-not-liouville`).
- Juschenko–Zheng's Question 5 for finitely generated groups, applied to a Liouville `F`-set with abelian
  stabilizers. Whether `F` has a LAT action with abelian stabilizers is not decided here. It would follow from a
  factorization `F = HK` with `H` amenable and `K` abelian.
