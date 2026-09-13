---
rg: 2
id: aperiodic-sft-gated-models-break-refinement-relations-proof
kind: route
title: At the gate boundary the coarse 3-cycle fires while every nested commutator of its refinements dies
target: aperiodic-sft-gated-models-break-refinement-relations
requires:
  - zd-derived-full-group-fp-forces-finite-type
---

**Constants.**
1. **Word lengths.** Each word `W(p, e)` with `p` on `B(R+1)` is obtained from generators by four
   nested-commutator steps. Its length is at most `C := 8^4`, independent of `R`. Every generator
   moves points by at most 2, so any word of length `<= C` moves points by at most `2C`.
2. **Radii.**
   - Put `K := 40C`.
   - Let `R_1^(K)` be a radius such that no legal `B(R_1^(K))`-pattern is compatible with its
     translate by any `u` with `0 < |u|_1 <= K`. It exists by ChJN's Lemma `lem:incompatible`
     (arXiv:1602.04255, line 126), which holds for any finite set of nonzero vectors.
   - Let `r_X` be a radius such that `X` is cut out by forbidden patterns on translates of
     `B(r_X)`.
   - Put `R_0 := max(R_1^(K) + 2, r_X)`. Fix `R >= R_0` and `rho >= R + K`.
   - `S` generates `G` because it contains ChJN's `𝒯_R` up to inverses.
3. **The key exclusion.** Let `m ∈ F` and `pi_0 = c|(m + B(R_1^(K)))`, which is legal. If
   `pi_0` occurs at `m'` with `0 < |m' - m|_1 <= K`, the union of the two windows lies in
   `m + B(R_1^(K) + K) ⊆ m + B(rho)`, which is legal. That contradicts the choice of `R_1^(K)`.
   So `pi_0` occurs at no other point within distance `K` of `m`.

**Item 1 (well defined).** If `s(pi, e)` fired at `m` and at `m' = m + g` with `0 < |g|_1 <= 2`,
then `pi_0 = pi|B(R_1^(K))` would occur at `m` and `m'`, contradicting step 3. So the triples of
the firing centres of `s` are disjoint.

**Item 2 (failure at the boundary).**
1. **The boundary point.** Since `F` is nonempty and not everything, there are `m ∈ F` and `h` with
   `|h|_1 = 1` and `m + h ∉ F`. Choose `e ⊥ h`. Put `pi = c|(m + B(R))`, which is legal.
2. **Left-hand side.** `s(pi, e)` fires at `m`, so it sends `m -> m + e`.
3. **Right-hand side, a single factor.** Let `p` be a legal extension of `pi` to `B(R+1)`, and put
   `p_h` for its sub-ball at centre `h`, translated to `B(R)`.
   - In ChJN's recursion for `W(p, e)` there is a step `j*` with `h_(j*) = h`. It is case (i),
     since `h ⊥ e`, so its second argument is the generator `b = s(p_h, h)`.
   - **`b` fires nowhere near `m`.** Suppose `b` fires at `m'` with `|m' - m|_1 <= K - 1`. Then
     `c|(m' + B(R)) = p_h`, and `p_h` contains `pi_0` at relative position `-h`. So `pi_0` occurs at
     `m' - h`, within distance `K` of `m`.
     - If `m' - h ≠ m`, step 3 is contradicted.
     - If `m' - h = m`, then `m' = m + h ∉ F`, so `b` does not fire there.
     - Either way `b` is the identity on `N_0 := m + B(K - 3)`.
   - **Local triviality propagates.** Let `a` be the word evaluated before step `j*`; it moves
     points by at most `2C`.
     - Then `[b, a] = b^(-1) a^(-1) b a` fixes every point of `N_0` whose image under `a` stays in
       `N_0`. So it is the identity on `N_1 := m + B(K - 3 - 2C)`, and similarly for
       `[b^(-1), a^(-1)]`.
     - So the step-`j*` word is the identity on `N_2 := m + B(K - 3 - 6C)`.
     - Each later step forms a commutator whose first argument is already the identity near `m`.
       By the same estimate it removes at most `6C` more from the radius.
     - At most four steps remain, so `W(p, e)` is the identity on `m + B(K - 3 - 30C)`. That ball
       contains `m`, since `K = 40C`.
4. **Conclusion.** Every factor of the right-hand side fixes `m`, so the product fixes `m`, while the
   left-hand side does not. The refinement relator for `(pi, e)` fails at `m`. ∎

**Item 3.** Refinement relators hold everywhere only if `F = ∅` or `F = Z^2`. If `F = Z^2`, every
`rho`-window of `c` is legal. Since `rho >= R >= r_X`, `c` contains no forbidden pattern of `X`, so
`c ∈ X`.

**Item 4.** A periodic `c ∈ X` would contradict freeness. So for periodic colourings satisfying
the refinement relators, `F = ∅` and all generators act trivially. Hypothesis (H1) of
`zd-subshift-full-group-lef-via-periodic-relator-shifts` needs some generator to move a point, so it
fails. ∎
