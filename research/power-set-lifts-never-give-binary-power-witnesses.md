---
rg: 2
id: power-set-lifts-never-give-binary-power-witnesses
kind: claim
title: The power-set lift of a strict automaton is never injective at size 2^k, and at size 2^k - 1 it is strict only for an unbalanced readable rule
distinct_from:
  clone-uniform-alphabet-changes-reach-only-boolean-powers: that kills alphabet changes respecting composition exactly; this treats the power-set lift, which respects composition only up to inclusion and so is not covered there.
  some-nonsurjunctive-group-gives-a-binary-power-one: that is the bridge; this closes one lax alphabet change, the natural move k -> 2^k, as a way to prove it.
  every-injective-ca-has-uniform-single-site-output-law: that asks every injective automaton to have a balanced rule; this shows the nonempty power-set lift of a strict automaton can be injective only when the rule is unbalanced, so that claim would make every such lift non-injective.
  strict-rule-pairs-ascend-to-larger-alphabets: that asks to extend strict rules to more symbols with the same memories; this asks for one specific extension, by sets of symbols, and shows its only power-of-two instance collapses.
artifacts:
  - experiments/hyperspace-lift-2026-09-17/check.py
  - experiments/hyperspace-lift-2026-09-17/check-output.json
---

**OPEN.** A drafted direct proof is recorded as an attempt (see Attempts). It is not established because one
referee lens refuted it on 2026-09-17: the numbered results were checked and hold, but part of the note is
asserted and proved nowhere, and the step-7 citation does not say what is used.

**Setting.**
- `tau` is a strict (injective, non-surjective) automaton on `A^G`, with `k = |A| >= 2`.
- Its local rule is `f: A^S -> A`, where `S` is the set of coordinates it depends on essentially.
- The **power-set lift** `Phi` on `P(A)^G` is `Phi(X)(g) = f(prod_{s in S} X(gs))`, the image set. It has
  `2^k` symbols. Its restriction to nonempty sets is `Phi*` on `P*(A)^G`, with `2^k - 1` symbols.
- `f` is **readable** if for every `a in A` there are `s in S` and `b in f(A^S)` with
  `f^(-1)(b) ⊆ {y : y_s = a}`.
- `f` is **balanced** if `|f^(-1)(b)| = k^(|S| - 1)` for every `b`.

**Claims.**
1. `|S| >= 2`.
2. `Phi` and `Phi*` are not surjective. Strictness comes for free, with no condition on the rule.
3. `Phi` is never injective. The empty set is an absorbing symbol.
4. If `Phi*` is injective, then `f` is readable.
5. If `f` is readable and balanced, then `f` depends on one coordinate. So by 1 and 4, `Phi*` injective forces
   `f` unbalanced, that is, `tau` has a non-uniform single-site output law.
6. If `f` is linear (over `F_p^d`) and `|S| >= 2`, then `f` is not readable. So `Phi*` is never injective
   for linear strict automata.
7. **Size moves.** The known moves are:
   - multiples `n -> nm`;
   - passing to a subgroup or overgroup (same size);
   - finite-index regrouping `n -> n^m`;
   - the nonempty lift `n -> 2^n - 1`.

   Each sends a size that is not a power of two to a size that is not a power of two. The one power-of-two lift,
   `n -> 2^n`, is never injective by 3. So **no finite sequence of regroupings, multiples and power-set lifts
   turns a failing size that is not a power of two into a binary-power witness.**

**Where this class dies.** At the empty set. The nonempty sets give the odd count `2^k - 1`. The one symbol
that would make it a power of two is `∅`, and it is absorbing: every window has at least two sites, so it can
never be read back. This is the one-extra-symbol annulus of the frontier notes, met again in a lax
construction.

**Computation.** Script `experiments/hyperspace-lift-2026-09-17/check.py`, output `check-output.json`.
- Over `Z` there are no strict automata, but injectivity of a lift depends only on the rule, so the census
  checks the injectivity criteria.
- **Ternary rules on window 2** (19683 rules). There are 48 injective rules. Of these, 36 depend on both
  coordinates. None is readable, and none has an injective lift, either on all subsets or on nonempty
  subsets. The 12 injective single-coordinate rules all have injective nonempty lifts.
- **Binary rules on window 3.** The 6 injective rules depend on one coordinate.
- **Explicit collision.** Take `tau(a,b)_i = (a_i, b_i + a_(i+1))` on `(F_2^2)^Z`. The all-`{(0,0),(1,1)}`
  configuration and the all-`A` configuration have the same lift.

**Still open inside this class.** Does an unbalanced readable strict rule have an injective nonempty lift?
That would give the size move `k -> 2^k - 1`, which changes the prime radical (`3 -> 7`, `5 -> 31`). It
cannot reach a power of two.

**Families of sets.** Restricting to a `tau`-closed family `F ⊆ P*(A)` that contains the singletons keeps
claim 2: strictness is free once the lift is injective. Such families include product designs
(`A_1 × {translation-closed sets of A_2}` for skew-product rules), so they cannot be killed as a class by size.
The unknown-symbol family `{singletons, A}`, when it is closed, has size `k + 1`. It dies by the same all-`A`
collapse unless for every `a` some coordinate `s` has `f({y_s = a}) ≠ f(A^S)`.

## Attempts

1. **Point selection for non-surjectivity, one-site collapse against the all-`A` background for
   non-injectivity (2026-09-17, refuted by referee).** Formerly route `power-set-lifts-binary-power-proof`,
   `requires: []`. The proof is kept as the attempt artifact
   `research/artifacts/power-set-lifts-binary-power-proof-2026-09-17.md`, together with
   `experiments/hyperspace-lift-2026-09-17/check.py` and `check-output.json`. Referee lens 1 returned
   *refuted*; lens 2 returned *survives* and found no gap in steps 1–7. Lens 1's reason, verbatim:

   > Refuted under the default rule: part of the claim is asserted but proved nowhere. The numbered results themselves hold up.
   >
   > What I checked and found correct in route power-set-lifts-binary-power-proof:
   > - Step 1 (|S| >= 2): a single-coordinate rule gives a bijection, so tau is onto.
   > - Step 2 (non-surjectivity): pick one point from each set.
   > - Step 3: the all-empty configuration and the one with X'(1)=A have the same lift, because every window has at least two sites.
   > - Step 4 (readability): take the all-A configuration and delete a at one site.
   > - Step 5 (balanced and readable gives one coordinate): each chosen preimage equals its cylinder, and cylinders on different coordinates meet.
   > - Step 6 (linear rules): ker f is contained in ker proj_s and has the same dimension, so f factors through proj_s.
   > - Step 7 arithmetic: nm, n^m and 2^n - 1 are not powers of two when n is not; the size 2^n comes only from Phi, which is never injective.
   > - I reran experiments/hyperspace-lift-2026-09-17/check.py and its output matches check-output.json exactly.
   > - I spot-checked the 36 two-coordinate injective ternary rules, e.g. (0,0,0,1,2,2,2,1,1). They are injective on periodic configurations up to period 6.
   >
   > First assertion with no proof (research/power-set-lifts-never-give-binary-power-witnesses.md, 'Families of sets' paragraph, around lines 64-70):
   > - It states that product designs 'A_1 × {translation-closed sets of A_2}' for skew-product rules are tau-closed families containing the singletons, 'so they cannot be killed as a class by size'.
   > - No step of the route proves this, and 'translation-closed' is defined nowhere in the repo.
   > - Read literally (sets closed under every translation of A_2), those sets would be only A_2 itself. The family would then contain no singletons, so it would not be an instance of the setting it is offered for.
   > - The same paragraph's criterion for the family {singletons, A} ('dies unless for every a some s has f({y_s=a}) ≠ f(A^S)') is correct by the same argument as step 4. It is also unproved in the route.
   >
   > Citation mismatch in step 7:
   > - It says 'every other size change used in the graph is a multiple, a subgroup or overgroup change, or a regrouping' and cites ec-groups-share-the-nonsurjunctive-alphabet-sizes.
   > - That claim states only NS(H) ⊆ NS(G) for H <= G and n -> nl. It contains no regrouping n -> n^m and no move to a subgroup.
   > - The other source cited is the attempt list of the OPEN claim some-nonsurjunctive-group-gives-a-binary-power-one. That list also records other size changes (star-symbol and reserved-symbol padding, clone-uniform maps).
   > - The route has requires: [] even though it imports these results.
   > - The formal statement of claim 7 is limited to the listed moves, so this does not break it, but the citation does not say what is used.
   >
   > Suggested fix: delete or prove the 'Families of sets' paragraph and define 'translation-closed'. Correct the step-7 citation and add the prerequisites to requires.

   - **To restore:** delete or prove the 'Families of sets' paragraph (defining 'translation-closed'), correct
     the step-7 citation, list the imported results in `requires`, and restore the artifact as a route once a
     full referee pass survives.
