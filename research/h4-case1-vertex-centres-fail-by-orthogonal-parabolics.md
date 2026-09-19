---
rg: 2
id: h4-case1-vertex-centres-fail-by-orthogonal-parabolics
kind: claim
title: Vertex centres fail for Case 1 in H_4 itself, in the target orientation, by an orthogonal-parabolic mechanism that works for every diagram s_1-s_2-s_3-(m)-s_4; the H_4 centralisers are not nested, so (H″) must be proved with non-vertex centres
distinct_from:
  h4-case1-commutator-helly-holds-in-type-a-but-vc-fails: that refutes VC only in type A_4, finds no VC failure in the H_4 balls, and leaves open whether the H_4 centralisers are nested; this refutes VC in H_4 (and B_4) with one uniform structural tuple, shows that the H_4 centralisers are not nested, and explains why the balls missed it.
  h4-case1-helly-is-a-commutator-double-coset-problem: that reduces Case 1 to (H″); this shows that the vertex-centre strengthening of (H″) is false in H_4, while (H″) holds for the tuple found.
---

**Setting.** Notation is as in `h4-case1-commutator-helly-holds-in-type-a-but-vc-fails` (w14).
- `Λ = s_1s_2s_3s_4` has `m_{s_1s_2} = m_{s_2s_3} = 3` and `m_{s_3s_4} = m`, with `m = 5` for the target (H_4).
- `X = {s_2,s_3,s_4}`, `Y = {s_1,s_2,s_3}` (type A_3), `F = ker(ρ_X|P_Y)` and `N = ker(ρ_Y|P_X)`.
- `[x,y] = xyx^{-1}y^{-1}`. VC fails for a tuple `(a,b,u,v)` with `[u,a] = [v,b] = k` iff `k ≠ 1`,
  `[u,b] ≠ k` and `[v,a] ≠ k`.
- In `F`, put `p_3 = s_1^2`, `p_2 = s_1s_2^2s_1^{-1}` and `p_1 = s_1s_2s_3^2s_2^{-1}s_1^{-1}`.

**Theorem.** Put
- `a = p_2p_3` and `b = p_1p_3`, so that `b = s_3^{-1}as_3`;
- `c = s_4^2`, `d = s_3^{-1}s_4^2s_3` and `w = (s_2s_3)s_4^2(s_2s_3)^{-1}`, all in `N`;
- `u = wc` and `v = wd`.

Then:
1. **(Structure, every `m ≥ 3`.)**
   - `c ∈ C_N(a)`, `d ∈ C_N(b)` and `w ∈ C_N(b^{-1}a)`.
   - Hence `[u,a] = [v,b] = [w,a] = k`, and `w ∈ U_a(k) ∩ U_b(k)`.
2. **(Certified, `m = 3, 4, 5`.)**
   - `k ≠ 1`, `[u,b] ≠ k` and `[v,a] ≠ k`.
   - `c ∉ C_N(b)` and `d ∉ C_N(a)`.
3. **Consequences.**
   - VC is false in H_4, in the orientation of the target, and also in B_4 and A_4.
   - `C_N(a)` and `C_N(b)` are incomparable, so the nesting route of w14 (Q.4) is dead in H_4.
   - (H″) holds for this tuple: `u^{-1}v = c^{-1}d ∈ C_N(a)C_N(b)`, and the centre comes from the common point `w`,
     not from a hexagon vertex.
4. **(Why the balls missed it.)** `u` has N-length 2, but `d` has N-length greater than 6 in H_4 (at most 5 in B_4
   and 3 in A_4) in the 12 meridian generators of `N`. So `v` lies outside the H_4 N-ball of radius 4 searched by
   w14.

**Mechanism.**
- The parabolic `A_{s_4}` is orthogonal to `A_{s_1s_2}`.
- `a` lies in `A_{s_1s_2}`, and `w^{-1}`-conjugation carries `b^{-1}a` into `A_{s_1s_2}`, where
  `(s_2s_3)^{-1}b^{-1}a(s_2s_3) = Δ_{12}^{-2}·s_1·s_1s_2·s_2s_1·s_1`.
- So three `A_Y`-elements share commuting `N`-elements coming from three different conjugates of `A_{s_4}`.
- The larger orthogonal complements in H_4 give more room for this: 15 roots orthogonal to a root, forming H_3, and
  3 orthogonal to two adjacent roots, forming A_2.

**What it leaves.**
- A proof of Case 1 of `h4-deligne-complex-bottom-triples-have-upper-bounds` must produce non-vertex centres in
  H_4 itself, as the `Z/2` Helly argument does in type A.
- The lifting test (L) of w14 is no longer needed to refute VC.
- The open statement is (H″) in H_4 alone. Since VC fails, no search over hexagon vertices can settle it.

**Status.** Established. Parts 1 and 3 are proved in the route. The inequalities in part 2 are certified twice:
- by exact Garside normal forms;
- by an exact `ℚ(√5)` reflection-type linear representation at `t = 2`, which satisfies the braid relations.

Part 4 is an exact meet-in-the-middle computation.
