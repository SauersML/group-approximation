---
rg: 2
id: fpbs-window-local-cost-lower-bounds-fail-at-bernoulli
kind: claim
title: Ergodic aperiodic shift measures that are exactly iid and free on arbitrarily large balls can have cost one, so no window-local hypothesis forces Bernoulli cost
distinct_from:
  fpbs-l2-gap-class-closed-under-local-limits: that shows a critical l2 gap survives local limits and that finite or amenable approximants never supply one; this is about cost itself on invariant shift measures converging to the Bernoulli point, and it shows that any lower bound for cost near that point has to use global freeness.
  fpbs-fixed-price-iff-cost-lsc-at-bernoulli: that equates fixed price with lower semicontinuity of cost at lambda^G along free measures; this shows the free hypothesis there cannot be replaced by freeness on a finite ball.
artifacts:
  - research/artifacts/fpbs-window-local-cost-lower-bounds-fail-at-bernoulli-proof-attempt-2026-09-17.md
---

**OPEN.** A drafted proof is recorded as an attempt (see Attempts). It is not established because the
referee vote of lens 1 was lost; lenses 2 and 3 returned *survives*.

Let `G` be a finitely generated residually finite group with an infinite amenable quotient
`p: G -> A`, `S` a finite symmetric generating set, `L` a finite set with `|L| >= 2`, and
`lambda` a probability vector on `L` with full support. For every `R` there is a `G`-invariant
Borel probability measure `nu_R` on `L^G` such that:

1. the marginal of `nu_R` on `L^{B_R}` is exactly `lambda^{B_R}`, so `nu_R -> lambda^G` weak*;
2. `nu_R(Fix gamma) = 0` for every `gamma ∈ B_R \ {1}`;
3. `G ↷ (L^G, nu_R)` is ergodic and every orbit is infinite;
4. its orbit relation has cost `1`.

Consequently, at `lambda^G` the cost jumps by at least `C(b) - 1 >= beta_1^(2)(G)` along
ergodic aperiodic measures that are iid and free on arbitrarily large balls, where `b` is a
nontrivial Bernoulli shift of `G`.

**Class kill.** Let `eta < beta_1^(2)(G)` for such a group. No inequality
`C(nu) >= C(b) - eta` holds for all invariant `nu` satisfying finitely many conditions of the
following kinds:
- closeness to `lambda^G` on a finite window, including exact equality there;
- ergodicity;
- aperiodicity;
- `nu(Fix gamma) = 0` for `gamma` in a finite ball.

The statement applies to every finitely generated residually finite group with infinite
abelianization and positive first L2 Betti number. Illustrations, with standard Betti values that
are not imported as nodes: free groups `F_r` with `r >= 2`, where the jump is at least `r - 1`, and
closed surface groups of genus at least 2.
A proof of fixed price through `fpbs-fixed-price-iff-cost-lsc-at-bernoulli` must therefore use
essential freeness of the approximating measures at a step that is not checked on a finite
window. The certificate transfer of `fpbs-clopen-certificate-cost-transfer`, which only ever
reads a window, can only prove upper bounds.

## Attempts

1. **Pull back the Bernoulli shift of an amenable quotient that is injective on a large ball (2026-09-17).**
   Formerly the route `fpbs-window-local-cost-lower-bounds-fail-at-bernoulli-proof` (requires
   [fpbs-amen2-cost-inputs, fpbs-amen2-betti-cost-input, abert-weiss-free-actions-weakly-contain-bernoulli,
   cost-is-constant-on-weak-equivalence-classes]); see
   `research/artifacts/fpbs-window-local-cost-lower-bounds-fail-at-bernoulli-proof-attempt-2026-09-17.md`.
   Demoted on 2026-09-17 after the referee audit of `fpbs-fixed-price-iff-cost-lsc-at-bernoulli`: the vote of
   lens 1 was lost, so the full referee pass required for ESTABLISHED did not complete. Lenses 2 and 3 returned
   *survives*, checking that `psi = (q,p)` is injective on `B_R`, that `T` is injective and equivariant, that
   `nu_R` has cost 1 as a Bernoulli shift of an infinite amenable group, and the Gaboriau bound
   `C(b) >= 1 + beta_1^(2)`. No mathematical error has been reported. Restore the route once a full referee
   pass survives.
