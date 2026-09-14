---
rg: 2
id: aperiodic-subshift-el-normal-subgroups-are-sandwiched-proof
kind: route
title: The note's tower commutator run modulo a subsystem gives the sandwich E_Y ≤ N ≤ ker π_Y
target: aperiodic-subshift-el-normal-subgroups-are-sandwiched
requires: [aperiodic-subshift-ring-ideals-are-invariant-open-sets]
artifacts:
  - research/artifacts/sk-open-1-subsystem-normal-subgroups-2026-09-13-part1.md
---

Full derivation: artifact §Tower facts, Lemma 2, Theorem 3 and Proposition 5.

Step 0. I_N = {r : e_12(r) ∈ N} is a two-sided ideal (permutation matrices and the elementary identities). The required ideal lemma gives a unique Y with I_N = I_Y.

Step 1. N ⊇ e_ij(I_Y) for all i ≠ j, so E_Y ≤ N.

Step 2. Suppose g ∈ N and π_Y(g) ≠ 1.
- The centre of EL_n(R_Y) is trivial: central elements of R_Y are invariant functions, and invertible F_2-valued functions equal 1.
- So some tower transvection h = e_ij(s), with s ∈ {e_C, e_C u^{±1}} for a partition C with C ∩ T^jC = ∅ for 0 < |j| ≤ 2w+3, has π_Y([g,h]) ≠ 1. Otherwise π_Y(g) commutes with a generating subring, hence is central, hence trivial.
- k = [g,h] ∈ N has a locally constant corner κ : U → GL_d(F_2), with d ≥ 3.
- Restriction sends E_ab(W) to E_ab(W ∩ Y). So κ(y) ≠ I for some y ∈ U ∩ Y. Take a clopen W ∋ y with κ|_W constant.
- Then H_W ≅ GL_d(F_2) lies in N (simplicity of GL_d(F_2)), so e_W ∈ I_N = I_Y and W ∩ Y = ∅. That is a contradiction.

Uniqueness. E_{Y'} ≤ N ≤ ker π_{Y'} forces I_{Y'} = I_N.

(b) St_n(R)/⟨⟨x_ij(I_Y)⟩⟩ ≅ St_n(R_Y), since generators and relations lift, and it maps onto G/E_Y. The composite with G/E_Y → EL_n(R_Y) is canonical, so ker π_Y / E_Y is the image of K_2(n, R_Y).
