---
rg: 2
id: fpbs-relative-susceptibility-divergence-crux-fails
kind: claim
title: Relative susceptibility need not diverge at the relative threshold, and critical relative finiteness does not force a relative gap
distinct_from:
  fpbs-tree-normal-relative-threshold-is-inverse-cogrowth: that is the exact formula for every normal subgroup of a free group on its tree; this records the explicit examples in which the divergence crux of the frontier map fails, with and without a gap.
  fpbs-relative-gap-along-any-subgroup-separates: that derives the gap from finiteness of chi^I_p at some p strictly above p_c(G); this shows that finiteness at p_c(G) itself does not give the gap, and that the gap can hold while chi^I stays finite at the relative threshold.
artifacts:
  - research/artifacts/fpbs-tree-relative-cogrowth-2026-09-16.md
  - research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md
---

**ESTABLISHED.** Section 7(d) of the frontier map calls `D(I)` the statement

```text
chi^I_p -> infinity   as   p ↑ p_c(I;G),
```

and notes that `D(I)` together with `chi^I_(p_c(G)) < infinity` gives
`p_c(G) < p_c(I;G)`, hence `p_c(G) < p_u(G)`. Both premises fail as general
principles, already for infinite normal subgroups of free groups on their
standard trees. Let `T` be the 6-regular tree `Cay(F_3, {a_1,a_2,a_3}^(±1))`,
so `p_c(T) = 1/5`.

1. **Critical relative finiteness without a gap.** For `N = [F_3,F_3]`,
   `p_c(N;T) = p_c(T) = 1/5`, and

   ```text
   chi^N_(1/5) = (4/5) G_(Z^3)(1) = 1.21310... < infinity,
   ```

   while `chi^N_p = infinity` for `p > 1/5`. So `D(N)` fails, and
   `chi^N_(p_c(T)) < infinity` does not give `p_c(T) < p_c(N;T)`.
2. **A gap without divergence.** For `N = <<a_3>>`, the normal closure of
   `a_3`,

   ```text
   p_c(N;T) = (2 + 2 sqrt 3 - sqrt(8 sqrt 3 - 4))/10 = 0.232461... > 1/5,
   chi^N_(p_c(N;T)) = phi(p_c(N;T)) (3 + sqrt 3) = 3.5241... < infinity,
   ```

   with `phi(s) = (1 - s^2)/(1 + 5 s^2)`. Here the relative gap holds, yet
   `D(N)` fails.
3. **Divergence without a gap.** On the 4-regular tree `Cay(F_2)`, the subgroup
   `N = [F_2,F_2]` has `p_c(N;T) = p_c(T) = 1/3` and `chi^N_(1/3) = infinity`.
   So `D(N)` holds and there is no gap.

**Consequences.**
- The crux decomposition of Section 7(d) is valid but not usable as a black
  box.
- Let `N ◁ F_d` with `rho_Q > rho_T`. By Kesten 1959 (not re-verified here)
  this covers every `N ≠ 1`. For such `N`, the relative gap occurs exactly when
  `rho_Q < 1`. By Kesten's amenability criterion, which is cited and used only
  for this reading, that means exactly that the quotient is nonamenable. The gap
  coexists with finite relative susceptibility at the relative threshold
  whenever the quotient walk is rho-transient.
- Heuristically, this suggests that a proof of `p_c(G) < p_c(I;G)` along a
  normal subgroup with nonamenable quotient should bound `chi^I_p` directly at
  some `p` above `p_c(G)`, rather than go through `D(I)`. This is the situation
  of the (R0) products in `fpbs-residual-price-one-non-ah-class-nonuniqueness`.
  The suggestion is not part of the claim.

The global thresholds of trees are not in question: `p_u(T) = 1`. The examples
bear only on the method.

**Proof.** `fpbs-relative-susceptibility-divergence-crux-fails-proof`, with
details in Section 6 of the artifact.
