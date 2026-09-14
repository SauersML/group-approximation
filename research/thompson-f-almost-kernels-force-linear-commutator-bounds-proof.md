---
rg: 2
id: thompson-f-almost-kernels-force-linear-commutator-bounds-proof
kind: route
title: The commutator lies in the normal closure of every nontrivial element, and Hamming distance is bi-invariant
target: thompson-f-almost-kernels-force-linear-commutator-bounds
requires: []
---

**Import (trust surface).** Every nontrivial normal subgroup of `F` contains `[F,F]`. It is pinned in
`thompson-f-is-lea-only-if-amenable-proof` (Burillo--Lodha--Reeves, arXiv:1509.04586, citing
Cannon--Floyd--Parry: every proper quotient of `F` is abelian) and used the same way in
`thompson-f-two-transitive-actions-are-faithful-proof`.

**1. Normal closure.** `w ≠ 1` in `F`, so the normal closure of `w` in `F` contains `[F,F]`, which
contains `c = [a,b] = a^-1b^-1ab`. So in `F`, `c = Π_(i=1)^M u_i w^(ε_i) u_i^-1` for some words `u_i`
and signs `ε_i`.

**2. Lift to the free group.** In the free group on `a, b`, the element
`c · (Π_i u_i w^(ε_i) u_i^-1)^-1` maps to `1` in `F`, so it lies in the normal closure of
`{R_1, R_2}`. It is therefore a product `Π_(k=1)^N v_k R_(j_k)^(δ_k) v_k^-1`. So, in the free group,

`c = Π_(k=1)^N v_k R_(j_k)^(δ_k) v_k^-1 · Π_(i=1)^M u_i w^(ε_i) u_i^-1`.

Here `M ≥ 1`, because `c ≠ 1` in `F` (`F` is nonabelian), so `c` is not in the normal closure of the
relators.

**3. Evaluate.** Substitute `(A, B)`. Bi-invariance of `d` gives `d(XY,1) ≤ d(X,1) + d(Y,1)`,
`d(UXU^-1, 1) = d(X,1)` and `d(X^-1,1) = d(X,1)`. So

`d(A^-1B^-1AB, 1) ≤ N · max_j d(R_j(A,B),1) + M · d(w(A,B),1)`,

and `d(A^-1B^-1AB, 1) = d(AB, BA)`, since `ABx ≠ BAx` exactly when `(BA)^-1AB` moves `x`. Take
`N_w = N` and `M_w = M`.

**4. Instances.**
- `x_0^L(t) = t/2^L` for small `t > 0`, so `a^L ≠ 1` in `F`, and likewise `x_1^L ≠ 1`. If `A^L = 1`,
  the last term vanishes.
- **Witnesses.** Rearranged, the inequality reads `d(w(A,B),1) ≥ (t - N_w D)/M_w`. ∎
