---
rg: 2
id: fpbs-lamplighter-fixed-list-morse-attainment-fails-proof
kind: route
title: Map Cayley cycles onto the cycle module of the finite-stabilizer quotient graph, which relators of depth K cannot touch
target: fpbs-lamplighter-fixed-list-morse-attainment-fails
requires:
  - fpbs-morse-mass-bounded-by-relator-boundary-rank
  - fpbs-bernoulli-morse-collapse-criterion
  - fpbs-amen2-cost-inputs
  - fpbs-amen2-betti-cost-input
artifacts:
  - research/artifacts/fpbs/docs/morse-l2-inequality-and-lamplighter-gap.md
  - experiments/fpbs-morse-l2-gap-2026-09-17/lamplighter_coset_cancellation.py
---

Written derivation, Section 4 of the artifact.

1. **Presentation.** In `<a, t | a^2, [a, a_k] (k >= 1)>` all `a_i = t^i a t^-i` commute, so the normal closure of
   `a` is a quotient of `⊕ Z/2`. It maps injectively onto the lamps, so the group is `Z/2 wr Z` and every finite list
   lies in some `N_(R_K)` (Lemma 4.1).
2. **Quotient chain map.** `phi_0 = p_A` (average over right `A`-cosets, trace `2^-(K+1)`) and `phi_1 = p_B pi_t`
   (kill `a`-edges, average `t`-edges over right `B`-cosets, trace `2^-K`). `phi_0 d1 = d^Y phi_1` because
   `t^-1 B t ⊆ A`.
3. **Cycle dimension of the quotient.** `d^Y` has dense range, since an invariant vector is constant on infinite
   orbits. So `dim ker d^Y = 2^-K - 2^-(K+1)`.
4. **Relators vanish.** On `[a, a_k]` the forward and backward `t`-edges differ by `a_(k-i)`, which is in `B`. So
   `phi_1 Z_R = 0`.
5. **Onto.** `psi(xi) = xi - omega d1 xi`, where `omega` fills zero-sum vectors on `A`-cosets with paths built from
   `t^k a t^-k` (`k <= K`), which `phi_1` kills. Then `phi_1 psi = id` on `ker d^Y`.
6. **Count.** `dim(ker d1 ⊖ Z_R) >= 2^-(K+1)`. Amenability gives `C(b) = 1` (`fpbs-amen2-cost-inputs`), hence
   `beta_1 = 0` (`fpbs-amen2-betti-cost-input`). So `gap(R) >= 2^-(K+1)`, and Theorem C gives
   `m(R) >= 2^-(K+1)`.
7. **Subgraphing cost.** `R_b` is hyperfinite (Ornstein–Weiss, [GL] = Gaboriau, *Around the orbit equivalence
   theory...*, lecture notes, Thm 1.13, as imported by the complete route
   `fpbs-amalgam-over-amenable-descends-fixed-price-proof`). Nested Kruskal forests of `Phi_S`-edges over a finite
   exhaustion give an acyclic generating subgraphing of cost at most 1. So `C_sub(S) = 1`, and by Theorem B(ii)
   `lim m(P_L) = 0`.
8. **Finite checks.** The script verifies the coset identities, the relator cancellation, the correction paths, and
   the non-cancellation of `[a, a_(K+1)]` for `K <= 5`. It exits 0.

This is a supplied deduction, not independent verification. Step 7 depends on the cited hyperfiniteness import. Steps
1–6, which give the failure of (Q1), do not.
