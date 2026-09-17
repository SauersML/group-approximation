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

**ESTABLISHED** by `power-set-lifts-binary-power-proof`.

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
