---
rg: 2
id: limit-groups-over-hyperbolic-groups-satisfy-boone-higman
kind: claim
title: Limit groups over a torsion-free hyperbolic group, and every finitely generated subgroup of its Lyndon completion, embed in finitely presented simple groups
distinct_from:
  hyperbolic-groups-satisfy-boone-higman: that is the base case Γ itself; this covers every finitely generated subgroup of the Lyndon completion Γ^{Z[t]}, which is not hyperbolic and, when Γ is not linear, not linear.
  finitely-generated-linear-groups-satisfy-boone-higman: that covers limit groups over free groups (they are linear; BBMZ survey Theorem 5.1(5)); limit groups over a non-linear hyperbolic group are not linear, so that route does not reach them.
  pbh-class-closed-under-centralizer-amalgams: that is the closure theorem used; this combines it with the Kharlampovich--Myasnikov embedding into iterated extensions of centralizers.
---

**ESTABLISHED** by `limit-groups-over-hyperbolic-bh-proof` (lane proof, not reviewed;
no priority claimed).

`𝒢` is the class of Kharlampovich--Myasnikov (JEMS 14 (2012), arXiv:0904.2423):
non-abelian torsion-free relatively hyperbolic groups with free abelian parabolic
subgroups. It contains every non-abelian torsion-free hyperbolic group (empty
family of parabolics).

## Statement

Let `Γ ∈ 𝒢` be finitely generated and in `B_A`; for example `Γ` a non-abelian
torsion-free hyperbolic group. Then every finitely generated subgroup of the
Lyndon completion `Γ^{Z[t]}` lies in `B_A`, hence embeds in a finitely presented
simple group. This includes:

1. every finitely generated `Γ`-group discriminated by `Γ` (equivalently, universally
   equivalent to `Γ` with constants; the limit groups over `Γ` in the sense with
   constants), and every finitely generated subgroup of one;
2. every coordinate group of an irreducible algebraic set over `Γ`;
3. every group obtained from `Γ` by finitely many extensions of centralizers
   `Γ_{i+1} = <Γ_i, t_i | [C_{Γ_i}(u_i), t_i] = 1>`.

For `Γ` a free group this recovers Boone--Higman for limit groups (BBMZ survey,
arXiv:2306.16356v3, Theorem 5.1(5)), which serves as a calibration.
