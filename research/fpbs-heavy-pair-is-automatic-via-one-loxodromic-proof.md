---
rg: 2
id: fpbs-heavy-pair-is-automatic-via-one-loxodromic-proof
kind: route
title: Nested decreasing pieces of the fundamental annuli of one loxodromic, with masses (i+1)^{-3/2}, give self-intersections equal to the tail sums, whose squares are not summable, while every non-fixed pair visits the product of the pieces only finitely often under that cyclic group
target: fpbs-heavy-pair-is-automatic-via-one-loxodromic
requires:
  - fpbs-invariant-boundary-squares-need-heavy-returns
  - fpbs-finite-fibre-bb-classes-are-boundary-squares
---

Full written proof. Notation is as in the target claim. All sets are Borel, and `m = lambda x lambda`.

## Imported inputs (standard hyperbolic dynamics)

- **(H1) Minimality.** For a nonelementary hyperbolic group, every orbit in `dGamma` is dense, and `dGamma` is a
  compact perfect metrizable space.
- **(H2) North--South dynamics.** A loxodromic `h` has exactly two fixed points `h^+ != h^-` in `dGamma`. For all
  open neighbourhoods `U^+` of `h^+` and `U^-` of `h^-`, there is `N` such that `h^n(dGamma \ U^-) ⊆ U^+` and
  `h^{-n}(dGamma \ U^+) ⊆ U^-` for all `n >= N`. A nonelementary group contains two loxodromics with disjoint fixed
  point sets.
- **(M) Measure theory.** A nonatomic sigma-finite measure takes every value in `[0, lambda(B)]` on Borel subsets of
  `B` (Sierpinski). A sigma-finite measure with `lambda(B) = infinity` has subsets of `B` of every finite mass. This
  uses sigma-finiteness to get a subset of finite mass at least the target, then (M) inside it.

## Proof of Lemma A

Suppose, for a contradiction, that `lambda(U) < infinity` for some nonempty open `U`.

1. By (H1), the translates `gU` cover `dGamma`. By compactness, finitely many do: `dGamma = g_1 U ∪ ... ∪ g_r U`.
2. By invariance, `lambda(dGamma) <= r lambda(U) < infinity`. Since `lambda != 0`, `nu = lambda / lambda(dGamma)` is
   a `Gamma`-invariant, nonatomic probability measure.
3. Take a loxodromic `h`, a closed set `F ⊆ dGamma \ {h^-}`, and an open neighbourhood `U^+` of `h^+`. Choose an open
   neighbourhood `U^-` of `h^-` disjoint from `F`. By (H2), `h^n F ⊆ h^n(dGamma \ U^-) ⊆ U^+` for large `n`, so
   `nu(F) = nu(h^n F) <= nu(U^+)`. Letting `U^+` decrease to `{h^+}` gives `nu(F) <= nu({h^+}) = 0`.
4. Exhausting the open set `dGamma \ {h^-}` by countably many closed sets gives `nu(dGamma \ {h^-}) = 0`. Also
   `nu({h^-}) = 0`, so `nu(dGamma) = 0`. This contradicts `nu(dGamma) = 1`.

So `lambda(U) = infinity`. (Without nonatomicity, the same argument puts all of `nu` on `{h^+, h^-}` for every
loxodromic `h`, and two loxodromics with disjoint fixed-point sets give the contradiction.) ∎

## Proof of Theorem B

**Step 1 (a loxodromic with nested neighbourhoods).**
- Choose open neighbourhoods `U^+` of `h^+` and `U^-` of `h^-` with disjoint closures.
- By (H2), choose `N` with `h^N(dGamma \ U^-) ⊆ U^+` and `h^{-N}(dGamma \ U^+) ⊆ U^-`, and put `f = h^N`.
- Since `cl U^+ ⊆ dGamma \ U^-`, we get `f(cl U^+) ⊆ U^+`. Likewise `f^{-1}(cl U^-) ⊆ U^-`.

So `U^+ ⊇ f U^+ ⊇ f^2 U^+ ⊇ ...` and `U^- ⊇ f^{-1} U^- ⊇ ...`.

**Step 2 (fundamental annuli).**
- Put `B^+ = U^+ \ f U^+` and `B^- = U^- \ f^{-1} U^-`.
- The sets `f^j B^+`, `j >= 0`, are pairwise disjoint, since `f^j B^+ = f^j U^+ \ f^{j+1} U^+` and the `f^j U^+` are
  nested. Likewise the sets `f^{-j} B^-`, `j >= 0`, are pairwise disjoint.
- `B^+` contains the open set `O^+ = U^+ \ f(cl U^+)`, which is nonempty. Otherwise `U^+ = f(cl U^+)` is closed,
  hence `U^+ = f^n U^+` for all `n`. But by (H2), `f^n U^+` shrinks into every neighbourhood of `h^+`, while `U^+` is
  a nonempty open set of a perfect space, hence not a single point.
- Likewise `B^-` contains a nonempty open set.
- By Lemma A, `lambda(B^+) = lambda(B^-) = infinity`.

**Step 3 (nested pieces).** Put `m_i = (i+1)^{-3/2}`. By (M), choose Borel sets
`B^- ⊇ C_0 ⊇ C_1 ⊇ ...` with `lambda(C_i) = m_i`, and `B^+ ⊇ C'_0 ⊇ C'_1 ⊇ ...` with `lambda(C'_i) = m_i`.
Define

`A1 = ⊔_{j >= 0} f^j C'_j ⊆ U^+`,  `A2 = ⊔_{j >= 0} f^{-j} C_j ⊆ U^-`.

These are disjoint unions by Step 2. By invariance, `lambda(A1) = lambda(A2) = sum_i m_i = zeta(3/2) < infinity`.
The closures lie in `cl U^+` and `cl U^-`, which are disjoint.

**Step 4 (the self-intersections).** Fix `k >= 1`.
- **For `A1`.** `f^k A1 = ⊔_j f^{j+k} C'_j` lies in the annuli `f^i B^+` with `i >= k`. At level `i >= k`, `A1` has
  `f^i C'_i` and `f^k A1` has `f^i C'_{i-k}`. Their intersection is `f^i (C'_i ∩ C'_{i-k}) = f^i C'_i`, because the
  pieces decrease. So `lambda(A1 ∩ f^k A1) = sum_{i >= k} m_i = T_k`.
- **For `A2`.** `f^k A2 = ⊔_j f^{k-j} C_j`. Its intersection with `A2` lives at the levels `f^{-i} B^-`, `i >= 0`,
  where `A2` has `f^{-i} C_i` and `f^k A2` has `f^{-i} C_{i+k}`. So `lambda(A2 ∩ f^k A2) = sum_{i >= 0} m_{i+k} = T_k`.

Since the product set satisfies `E ∩ f^k E = (A1 ∩ f^k A1) x (A2 ∩ f^k A2)`, we get `m(E ∩ f^k E) = T_k^2`.

Comparing with the integral gives `T_k >= ∫_{k+1}^∞ x^{-3/2} dx = 2 (k+1)^{-1/2}`. So `T_k^2 >= 4/(k+1)`, and
`sum_{k >= 1} T_k^2 = infinity`. Since `m(E ∩ g^{-1}E) = m(gE ∩ E)` by invariance, the terms `g = f^{-k}` of `R(E)`
alone give `R(E) >= sum_{k >= 1} T_k^2 = infinity`. This proves item 1.

**Step 5 (finitely many cyclic returns).** Let `(xi, eta) in E` with `xi, eta` not in `{h^+, h^-}`. This excludes an
`m`-null set, since `lambda` is nonatomic.
- `xi in f^i C'_i ⊆ f^i B^+` for a unique `i >= 0`. Also `f^k xi in f^{i+k} B^+`, which meets `A1 ⊆ ⊔_{j >= 0} f^j B^+`
  only if `i + k >= 0`.
- `eta in f^{-i'} B^-` for a unique `i' >= 0`. Also `f^k eta in f^{k-i'} B^-`. Since `f^{k-i'} B^- = f^{-(i'-k)} B^-`,
  this meets `A2` only if `i' - k >= 0`.

So `f^k (xi,eta) in E` forces `-i <= k <= i'`, a finite set. This proves item 2. ∎

## Proof of Corollary C

`K1 = cl A1` and `K2 = cl A2` are compact and disjoint.
- Theorem 2 of `fpbs-invariant-boundary-squares-need-heavy-returns` gives
  `R(A1 x A2) <= C_0 + sum_{|g| >= n_0} (a_g b_g + a'_g b'_g)`, with `C_0 < infinity`.
- The left side is infinite by Theorem B. So `sum_g a_g b_g + sum_g a'_g b'_g = infinity`.
- By definition, `a'_g` and `b'_g` are `a_g` and `b_g` with `A1` and `A2` exchanged. So one of the ordered pairs has
  a divergent sum, which is (heavy-pair) for it.
- Existence of an ergodic, nonatomic, sigma-finite invariant `lambda`: Proposition 5 of
  `fpbs-finite-fibre-bb-classes-are-boundary-squares`.
- `F_2`: Corollary 6.2 of the same node rules out conservative squares.

Item 2 is Step 5 together with the observation that every `f^{-k}` has attracting point `h^-`. ∎

## Sanity checks

- **Consistency with Corollary 4.2 of the w19 node** (nonatomic implies the maxima `alpha_n`, `beta_n` tend to `0`).
  Here the heavy self-returns are `T_k -> 0`, and only `sum T_k^2` diverges. This is the regime `c_n ~ n^{-1/2}`, whose
  products `c_n^2 ~ 1/n` are not summable. It is allowed by Theorem 3 there.
- **Consistency with conservativity theory.** `R(E) = ∫_E N dm` with `N` the return count. On `F_2`, `N` is finite a.e.
  on `E` (no conservative square), yet `∫_E N = infinity` on a set of finite measure. Nothing forbids this, and Step 5
  exhibits it directly for the cyclic part of `N`.
