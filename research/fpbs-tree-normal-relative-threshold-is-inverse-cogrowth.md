---
rg: 2
id: fpbs-tree-normal-relative-threshold-is-inverse-cogrowth
kind: claim
title: On the free-group tree the relative threshold of a normal subgroup is its inverse cogrowth, with susceptibility given by the quotient Green function
distinct_from:
  fpbs-relative-gap-along-any-subgroup-separates: that proves p_c(I;G) <= p_u(G) and the gap criterion for any infinite subgroup of any Cayley graph; this computes p_c(N;T) and chi^N_p exactly, including at the relative threshold, but only for normal subgroups of a free group on its standard tree.
  fpbs-hp-relative-sharpness: that gives exponential tails below p_c(H;G) on every Cayley graph; this identifies p_c(N;T) with the inverse cogrowth of N and evaluates chi^N_p up to and at the threshold, on trees only, and its proof does not use sharpness.
artifacts:
  - research/artifacts/fpbs-tree-relative-cogrowth-2026-09-16.md
---

**ESTABLISHED.**

**Setting.**
- Let `d >= 2` and `q = 2d - 1`. Let `T` be the standard Cayley graph of
  `F_d`, the `(q+1)`-regular tree, with `p_c(T) = 1/q`.
- Let `N ◁ F_d`, `Q = F_d/N`, and let `mu` be the image in `Q` of the uniform
  measure on the free basis letters and their inverses.
- Put `p_n = mu^(*n)(e)`, let `rho_Q = limsup p_n^(1/n)`, and let
  `G_Q(w) = sum_n p_n w^n`.
- Let `f_n(N)` be the number of elements of `N` of word length `n`, and let
  `R_N` be the radius of convergence of `sum_n f_n(N) s^n`.
- Write `z(s) = s/(1 + q s^2)`, `phi(s) = (1 - s^2)/(1 + q s^2)`, and
  `chi^N_p = E_p|K_o ∩ N|`.

Assume `rho_Q > 2 sqrt(q)/(q+1)`, the spectral radius of `T`. Let `s_N` be the
unique `s in (0, 1/sqrt q)` with `(q+1) z(s) = 1/rho_Q`. Then:

1. `R_N = s_N`, and for `0 <= p <= s_N`, in `[0, infinity]`,

   ```text
   chi^N_p = sum_n f_n(N) p^n = phi(p) G_Q((q+1) z(p)),
   ```

   while `chi^N_p = infinity` for `p > s_N`.
2. `p_c(N;T) = s_N`. The existence of an `N`-infinite cluster has probability
   `0` for `p < s_N` and `1` for `p > s_N`.
3. `chi^N_(s_N) = lim_(p ↑ s_N) chi^N_p = phi(s_N) G_Q(1/rho_Q)`. So `chi^N`
   diverges at the relative threshold iff `mu` is rho-recurrent, that is, iff
   `G_Q(1/rho_Q) = infinity`.
4. `p_c(T) < p_c(N;T)` iff `rho_Q < 1`.
5. At `p_c(T)`, `chi^N_(1/q) = ((q-1)/q) G_Q(1)`. This is finite iff the
   quotient walk is transient.

Item 1 is Grigorchuk's cogrowth formula, written as an analytic identity, and
item 4 is his cogrowth criterion read as a percolation statement. No novelty is
claimed for those. Item 2 is of the same kind as Lyons' theorem `p_c = 1/br`
for percolation on trees (Lyons 1990, not re-read here), applied to the subtree
spanned by `N`, although it does not follow from it verbatim, since an infinite
cluster in that subtree need not meet `N` infinitely often. No strong novelty
claim is made for item 2 either. The endpoint evaluations, items 3 and 5, were
not found stated in the literature that was checked. That search was cut short,
so this is weak evidence. The proof given here is self-contained.

**Proof.** `fpbs-tree-normal-relative-threshold-is-inverse-cogrowth-proof`,
with details in Sections 2–5 of the artifact.
