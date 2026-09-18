---
rg: 2
id: fpbs-branching-barrier-certificates-spectral-floor-proof
kind: route
title: Level sets of the longest D-free descent expand by the Kesten gap at every step, cannot jump the forbidden window around one half, and so never reach measure zero
target: fpbs-branching-barrier-certificates-spectral-floor
requires:
  - kesten-amenable-stabilizer-uniform-gap
  - burton-kechris-tempered-actions-koopman-bernoulli
artifacts:
  - research/artifacts/fpbs-branching-barrier-certificates-spectral-floor-2026-09-17.md
  - experiments/branching-barrier-2026-09-17/check.py
---

Full proof in the artifact, §1 for Theorem A and Lemma G and §2 for
Corollary B.

1. **Level sets.** Put `A_0 = X \ D` and
   `A_{j+1} = (X \ D) ∩ ∪_i c_i^{-1} A_j`. Then `A_j` is the set of points
   with a `D`-free forward path of length `j`. By König's lemma,
   `⋂ A_j` is the set of points with an infinite `D`-free path. So `D` is a
   barrier iff `alpha_j = mu(A_j) -> 0`.
2. **Expansion.** For `{i,j} ∈ P`,
   `mu(c_i^{-1}A ∪ c_j^{-1}A) = mu(A) + mu(A △ s_{ij}A)/2`. Here
   `mu(A △ sA) = ||f - s f||^2` with `f = 1_A - mu(A)`. Averaging over `P`
   and applying (GH) gives
   `mu(∪ c_i^{-1}A) >= mu(A) + eta mu(A)(1 - mu(A))`.
3. **Recursion.** `∪ c_i^{-1}A_j ⊆ A_{j+1} ∪ D` gives
   `alpha_j + eta alpha_j(1 - alpha_j) <= alpha_{j+1} + delta`. With
   monotonicity this yields:
   - (R1) `eta alpha_j(1 - alpha_j) <= delta`;
   - (R2) steps of size at most `delta`.
4. **Window.** Suppose `delta < delta_*`.
   - By (R1), every `alpha_j` avoids `(r_-, r_+)`.
   - That window has width `sqrt(1 - 4delta/eta)`, which is greater than
     `delta`.
   - `alpha_0 = 1 - delta >= r_+`, and by (R2) the sequence cannot jump the
     window.
   - So `alpha_j >= r_+ > 1/2` for all `j`, which is not a barrier.
5. **Lemma G.** Kesten, as quoted in `kesten-amenable-stabilizer-uniform-gap`:
   "rho = rho(A,S) = || (1/|S|) sum over s in S of lambda_A(s) || < 1 ...
   which is < 1 exactly when A is nonamenable." This gives
   `sum_S ||f - sf||^2 >= 2|S|(1 - rho)||f||^2` on `lambda_L`.
   - It passes to multiples of `lambda_L`, and to representations weakly
     contained in `lambda_L`, because norms in the group algebra do not
     increase under weak containment.
   - `burton-kechris-tempered-actions-koopman-bernoulli` quotes
     "κsΓ0 ∼= ∞ · λΓ", together with downward closure of tempered actions.
   - Restricted to `L`, `∞·lambda_Gamma` is `∞·lambda_L`.
6. **Corollary B.** In `M`, `c_1 c_2^{-1} = b` and `c_2 c_3^{-1} = a^{-1}`.
   The script checks these words in `F(a,b)`, since `c_i c_j^{-1}` cancels
   the `t`. `<a, b>` is the free base group `F_2` of the HNN extension.
   Taking `P = {{1,2},{2,3}}` gives `eta = 1 - rho`.

The value `rho(F_2) = sqrt(3)/2`, which gives the number `0.03346`, is
classical. It is not load-bearing, because the claim states the floor as
`delta_*(1 - rho)`.
