---
rg: 2
id: toms-twisted-swap-pairs-are-totally-degeneracy-forcing
kind: claim
title: In Toms's tower every small projection's two twisted halves form a totally degeneracy-forcing pair at all later stages, and no contraction transports one half to the other better than zero in uniform 2-norm
distinct_from:
  toms-ah-counterexample-to-uniform-gamma: that imports Toms's one obstruction pair (p_i, q_i), built from the trivial and tautological bundles on Gr(d,2d); this proves the same total rigidity for the twisted halves of an arbitrary projection of rank at most sqrt(2) d_r, at every level r and every scale.
  toms-schubert-algebra-fails-o6-plus: that bounds common Cuntz lower bounds of Toms's pair; this bounds approximate transports between twisted halves, at every scale.
  toms-schubert-algebra-continuous-ranks-are-constant: that is the rigidity conjecture for continuous ranks; this is a proved ingredient, showing that support rotated uniformly across all copies between twisted halves is lost entirely at some point.
---

Let `A = lim (A_i, phi_i)` be the non-simple limit of Toms's Section 4
(arXiv:2606.12188v2): `rank q_i = d_i`, `d_(i+1) = 2 d_i`,
`X_(i+1) = X_i x X_i x CP^(j_i)` with `j_i = 2 d_i^2`, and twists
`gamma_(i,1), gamma_(i,2)` pulled back from `O(1), O(2)`.

**Theorem.** Fix `r >= 1` and a projection `E in M_k(A_r)` of constant rank `w`
with `w <= sqrt(2) d_r`. Put

```text
E_1 = pi_1^* E tensor gamma_(r,1),     E_2 = pi_2^* E tensor gamma_(r,2)     in M_k(A_(r+1)),
```

the two orthogonal halves of `phi_r(E)`.
1. **Forcing at every stage.** For every `n >= r + 1`, every bundle map
   `phi_(r+1,n)(E_1) -> phi_(r+1,n)(E_2)` over `X_n` vanishes at some point.
2. **Equal traces.** `tau(E_1) = tau(E_2) = w/(2 k d_r)` for every
   `tau in T(A)`, normalized in `M_k`.
3. **Transport is useless.** Every contraction `y in E_2 M_k(A) E_1` satisfies

   ```text
   ||E_1 - y* y||_(2,u)^2  >=  w/(2 k d_r)  =  ||E_1||_(2,u)^2,
   ```

   so `y = 0` is already optimal. In particular `E_1` and `E_2` are not
   Murray–von Neumann equivalent in `M_k(A^u)`.
4. **Simple algebra.** In Toms's simple `B`, when `E` lies in the old corner at
   stage `m` of the telescoped system,

   ```text
   ||E_1 - y* y||_(2,u) >= delta sqrt(w/(2 k d_r)) - sqrt(eta_m)
   ```

   for every contraction `y in E_2 M_k(B) E_1`, with Toms's survival data
   `delta` and `eta_m` (Proposition 4). So the halves are not equivalent in
   `M_k(B^u)` once `sqrt(eta_m) < delta sqrt(w/(2 k d_r))`.

Toms's pair is the case `E` of rank `d_r` built from `(p_r, q_r)`. Here `E` is
arbitrary and may be tiny, for instance one leaf line `theta^1 tensor gamma_l`,
with `w = 1`.

**Correction to the dilution heuristic** in `toms-schubert-algebra-misses-a-rank`.
- There, moving `M` directions between twisted halves at level `r` was estimated
  to cost at most `sqrt(2) d_r / d_N` at stage `N`. That estimate holds for a
  swap made in **one copy** of the level-`r` node.
- If the same pair is swapped in **all** `2^(N-r-1)` copies, the transports form
  a bundle map between the pushforwards. By part 1 this map vanishes at one
  point, where the whole pushforward of `E_1` is lost: normalized loss
  `w/(2 k d_r)`, a fixed fraction independent of `N`.
- So only copy-dependent, non-uniform rotations dilute.

**Model test.**
- *Twists are load-bearing.* Take `E = theta^w` trivial. With trivial twists
  both halves are the trivial bundle `theta^w`, the identity is a
  nowhere-vanishing bundle map, and parts 1 and 3 fail. With Toms's twists
  `O(1), O(2)` the same `E` gives a forced pair.
- *Rank bound is load-bearing.* The proof needs `u^(w^2) != 0` in `CP^(j_r)`,
  that is `w^2 <= 2 d_r^2`.
- *Real object.* Toms's pair satisfies it.

Proof: `toms-twisted-swap-pairs-forcing-proof`. The mechanism is Toms's
(Lemma 1 and Theorems 2 and 5). The new content is its application to arbitrary
twisted halves and the sharp "no better than zero" bound. Internal derivation,
unreviewed.
