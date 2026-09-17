---
rg: 2
id: folding-act-certificates-reduce-to-core-permutation-models-proof
kind: route
title: Decode at good sites, avoid the pattern at window-good outputs, then propagate near-bijectivity along the core closure
target: folding-act-certificates-reduce-to-core-permutation-models
requires: []
artifacts:
  - research/artifacts/folding-act-certificates-2026-09-17.md
---

This route is self-contained. The artifact gives every step and constant.

1. **Theorem A.** Forward sufficiency decodes the input at each good site (Lemma 1), so the
   model automaton has at least `|A|^|V_0|` outputs. At a window-good output every output avoids
   the unique lift of `p` (Lemma 2, using (GoE) and injectivity of distinct pattern cells).
   Disjoint windows cap the outputs at `|A|^|U| (1-|A|^-|Omega|)^|U_1|`.
2. **Lemma 0.** Collapse the bad sites to one point by a non-injective view. Equalities and
   marked returns survive, and window distinctness lives in `U`. So the slack
   `D = |U| - |V_0|` controls all exceptions.
3. **Lemma 3.**
   - Near-bijectivity composes additively.
   - If `f' f` agrees with a near-bijection on `V_0`, then `f` and `f'` are near-bijections with
     the error increased by `2 lambda`.
4. **Theorem B(1).** Induct along the core closure: identity letters, marked pairs, then
   one-sided propagation along relators. Each step at most triples the error.
   **Theorem B(2).** Replace each core letter by a permutation, through the bijection
   `iota : U -> V` that extends `b_1^-1` on `V_0`. Relators hold on `V_0`, so the defect is
   bounded by the exceptions.
5. **Theorem B(3).** At a window-good output, the `Pi`-chain gives
   `iota g_w' u = h(pi) iota g_w u`, and the two points differ. Each exception point lies in
   one window only.
6. **Corollary B1.**
   - (i) Normalized defect tends to 0 while the moved fraction stays bounded below, which
     contradicts invisibility.
   - (ii) Disjoint copies followed by Lemma 0 turn an exact act into a density family.
7. **Proposition C.** The act on `(Omega x M)/~` has:
   - `b_s = id`;
   - `a_m[w,1] = [w,m]`, well defined by closure (iii), and the identity elsewhere;
   - one output whose window is `([w,1])_w`.

   All sites are good by closure (ii), the output is window-good by (i), and Theorem A gives
   `|V| <= |V| - kappa`.
