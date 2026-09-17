---
rg: 2
id: fpbs-relative-threshold-commensurability-invariant-proof
kind: route
title: Pigeonhole a cluster onto one coset, translate it home, and glue it to the origin with insertion tolerance
target: fpbs-relative-threshold-commensurability-invariant
requires:
  - fpbs-monster-groups-have-only-finite-amenable-subgroups
---

Let `I <= J` with `J = j_1 I ∪ ... ∪ j_k I`, a finite disjoint union of left
cosets. Write `C_H(p)` for the event that some cluster meets `H` in infinitely
many vertices. Since `C_H` is invariant under the ergodic action of `Gamma` by
left multiplication, `P_p(C_H) in {0,1}`, and `p_c(H;G) = inf{p : P_p(C_H) = 1}`.
By monotonicity in `p` (standard coupling), this infimum is a threshold.

**`p_c(J;G) <= p_c(I;G)`.** Since `I ⊆ J`, `C_I ⊆ C_J`.

**`p_c(I;G) <= p_c(J;G)`.** Let `p > p_c(J;G)`, so `C_J` holds a.s.

1. **Pigeonhole.** A cluster `K` with `|K ∩ J| = infinity` has
   `|K ∩ j_i I| = infinity` for some `i`, because `K ∩ J` is the finite union of
   the sets `K ∩ j_i I`. So `P_p(E_i) > 0` for some `i`, where `E_i` is the
   event that some cluster meets `j_i I` infinitely.
2. **Translate home.** Left multiplication by `j_i^{-1}` is an automorphism of
   `Cay(Gamma,S)`, since edges `g ~ gs` go to `j_i^{-1}g ~ j_i^{-1}gs`. It
   preserves Bernoulli measure, maps clusters to clusters and maps `j_i I` onto
   `I`. So `P_p(C_I) = P_p(E_i) > 0`.
3. **Zero-one law.** The zero-one law above gives `P_p(C_I) = 1`, so
   `p >= p_c(I;G)`.

(The same conclusion holds for the version "`|K_o ∩ I| = infinity` with positive
probability". On `C_I` some vertex `x` has `|K_x ∩ I| = infinity`. The event
`{|K_x ∩ I| = infinity}` is increasing, and `P_p(o <-> x) >= p^{|x|} > 0`, so
Harris--FKG gives `P_p(|K_o ∩ I| = infinity) > 0`.)

Taking `J = Gamma` gives `p_c(I;G) = p_c(Gamma;G) = p_c(G)` for finite-index
`I`.

**Corollary.**

- **Every infinite subgroup gives no gap.** If every infinite subgroup of
  `Gamma` has finite index, then every infinite `I` satisfies
  `p_c(I;G) = p_c(G)`. So condition 1 of
  `fpbs-relative-gap-along-any-subgroup-separates`, `p_c(G) < p_c(I;G)`, fails
  for all `I`. Condition 2 fails directly as well. For `p > p_c(G) = p_c(I;G)`
  the parenthetical above gives `P_p(|K_o ∩ I| = infinity) > 0`, so
  `chi^I_p = E_p|K_o ∩ I| = infinity`.
- **Torsion Tarski monsters.** For Ol'shanskii's torsion Tarski monster every
  proper subgroup is finite (cyclic of prime order), so every infinite subgroup
  is the whole group. The group is nonamenable and infinite by
  `fpbs-monster-groups-have-only-finite-amenable-subgroups`, so the hypothesis
  holds.

∎
