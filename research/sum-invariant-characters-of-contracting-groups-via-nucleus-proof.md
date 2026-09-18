---
rg: 2
id: sum-invariant-characters-of-contracting-groups-via-nucleus-proof
kind: route
title: Extend a nucleus function additively level by level; the two finite conditions are exactly what the product rule for sections needs
target: sum-invariant-characters-of-contracting-groups-via-nucleus
requires: []
artifacts:
  - experiments/contracting-polynomial-activity-2026-09-17/autgrp.py
  - experiments/contracting-polynomial-activity-2026-09-17/sumchar.py
---

Notation is that of the claim. `X^k` is the set of words of length `k`. Every `h in G` permutes `X^k`, and
`(gh)|_v = g|_{h(v)} h|_v`. Write `L(f)` for the least `L` with `f|_v in N` for all `|v| >= L`.

## 1. The theorem

Fix `I: N -> Q` with `I(1) = 0`, satisfying (i) and (ii).

**Step 1: `χ_I(f)` does not depend on `k >= L(f)`.** Let `k >= L(f)`. Then `f|_v in N` for every `v` with
`|v| = k`. By (i),

    Σ_{|v|=k+1} I(f|_v) = Σ_{|v|=k} Σ_x I((f|_v)|_x) = Σ_{|v|=k} I(f|_v).

So `χ_I` is a well-defined function on `G`. Since `L(n) = 0` for `n in N`, it satisfies `χ_I(n) = I(n)` there.

**Step 2: `χ_I(f) = Σ_{|u|=j} χ_I(f|_u)` for every `j >= 0`.** Here `(f|_u)|_w = f|_{uw}`, so `L(f|_u) <= L(f)`. For
`k >= L(f)`, Step 1 gives

    χ_I(f) = Σ_{|v|=j+k} I(f|_v) = Σ_{|u|=j} Σ_{|w|=k} I((f|_u)|_w) = Σ_{|u|=j} χ_I(f|_u).

With `j = 1` this is sum-invariance.

**Step 3: `χ_I` is a homomorphism.** Let `g, h in G` and `k >= max(L(g), L(h))`. For `|v| = k` both `g|_{h(v)}` and
`h|_v` lie in `N`. Step 2 and then (ii) give

    χ_I(gh) = Σ_{|v|=k} χ_I(g|_{h(v)} h|_v) = Σ_{|v|=k} [ I(g|_{h(v)}) + I(h|_v) ] = χ_I(g) + χ_I(h),

because `v ↦ h(v)` is a bijection of `X^k`.

**Converse.** Let `χ` be a sum-invariant character and `I = χ|_N`.

- Then (i) is sum-invariance applied on `N`.
- Iterating sum-invariance gives `χ(f) = Σ_{|v|=k} χ(f|_v)` for all `k`. For `k >= L(f)` this equals `χ_I(f)`.
  So `χ = χ_I`, and (ii) is additivity of `χ` on `n_1 n_2`.
- So restriction to `N` is injective, and its image is the solution space of (i)–(ii). It is clearly linear.

∎

## 2. The contraction certificate

Let `S` be a finite automaton generating `G`, closed under inverses, and let `N` satisfy the three conditions of the
effective version.

**Lemma.** Let `f` be finite-state with section set `Q(f) = {f|_v}`. Suppose every section of `f` lying on a cycle of
its section graph is in `N`. Then `f|_v in N` for all `|v| >= |Q(f)|`.

*Proof.* Let `|v| = m >= |Q(f)|`. The chain `f, f|_{v_1}, f|_{v_1v_2}, ..., f|_v` has `m + 1 > |Q(f)|` entries, so
two coincide: `f|_u = f|_{uw}` with `uw` a prefix of `v` and `w` nonempty. So `f|_u` lies on a cycle and is in `N`.
Since `N` is closed under sections, `f|_v = (f|_u)|_{u'}` is in `N`, where `v = uu'`. ∎

Apply the Lemma to the states of `S` and to the finitely many products `n_1 n_2`. This gives constants `K_S` and `K`:

- each generator has `L(s) <= K_S`;
- `L(n_1 n_2) <= K` for all `n_1, n_2 in N`.

For a word `g = g' g''` in the generators, `(g'g'')|_v = g'|_{g''(v)} g''|_v`. For `|v| >= max(L(g'), L(g''))` this
is a product `n_1 n_2`, so `L(g) <= max(L(g'), L(g'')) + K`. By induction on word length every `g` has finite
`L(g)`. So `G` is contracting and `N` has the property the theorem needs. ∎

**Exactness.**

- Two finite-state elements are equal if and only if they are equivalent under the Moore-machine partition refinement
  of any section-closed finite set of words containing both. The refinement starts from the root permutation and
  refines by the classes of the `d` sections, which decides equality exactly.
- `χ_I(n_1 n_2)` is computed by recursing through sections of `n_1 n_2` until they land in `N`.
  - By the Lemma, the recursion terminates.
  - It memoizes on classes, so a cycle outside `N` would be an infinite recursion, not a silent error.
- Conditions (i) and (ii) are linear equations with integer coefficients, solved over `Fraction` in `sumchar.py`.
