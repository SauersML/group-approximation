---
rg: 2
id: free-centre-by-metabelian-groups-linear-iff-residually-finite
kind: claim
title: For r >= 4, the free centre-by-metabelian group F_r/[F_r'',F_r] is linear in characteristic zero exactly when it is residually finite
distinct_from:
  free-centre-by-metabelian-groups-satisfy-boone-higman: that asks for membership in B_A for every rank and stays OPEN; this reduces the ranks r >= 4 to residual finiteness of C_r, which would give that membership.
  free-centre-by-metabelian-group-of-rank-two-is-linear: that settles rank 2 outright with an explicit representation; this is a reduction for r >= 4, where the explicit representation cannot be faithful because of torsion.
---

**ESTABLISHED as a reduction** (lane proof, elementary). It rests on one citation that was
read at abstract level only: C. K. Gupta, "The free centre-by-metabelian groups",
J. Austral. Math. Soc. 16 (1973) 294–299. Per the abstract, for `n >= 4`:
- `G_n = F_n/[F_n'', F_n]` has a finite elementary abelian subgroup `H_n`, fully
  invariant and contained in the centre;
- `G_n/H_n` is isomorphic to a group of 3x3 matrices over a finitely generated integral
  domain of characteristic zero.

## Statement

For `r >= 4` the following are equivalent:
1. `C_r = F_r/[F_r'', F_r]` is linear over a field of characteristic zero;
2. `C_r` is residually finite;
3. some finite quotient of `C_r` is injective on `H_r`.

When they hold, `C_r` lies in `B_A` (by `char-zero-linear-groups-satisfy-permutational-boone-higman`),
which is the rank-`r` case of `free-centre-by-metabelian-groups-satisfy-boone-higman`.

## Proof

- **1 ⇒ 2:** Mal'cev: finitely generated linear groups are residually finite.
- **2 ⇒ 3:** `H_r` is finite. For each `1 ≠ h ∈ H_r`, choose a finite quotient in which
  `h` survives. The product of these finitely many quotient maps is a finite quotient
  injective on `H_r`.
- **3 ⇒ 1:** Let `π: C_r -> Q` be finite and injective on `H_r`. The map
  `C_r -> C_r/H_r × Q` has kernel `H_r ∩ ker π = 1`.
  - `C_r/H_r` embeds in `GL_3(K)`, `K` the fraction field of Gupta's domain.
  - `Q` embeds in `GL_|Q|(Q) ⊆ GL_|Q|(K)` by its regular representation.
  - Block-diagonally, `C_r` embeds in `GL_(3+|Q|)(K)`. ∎

## Resolved (2026-09-18)

All three conditions hold for every `r`: `free-centre-by-metabelian-groups-are-linear`. The
finite quotient in (3) comes from the nilpotent quotient `C_r/γ_7(C_r)`, by Gupta–Levin 1986,
Lemma 4.4. The notes below are the state before that.

## What was open

- Residual finiteness of `C_r` for `r >= 4`. Gupta and Wehrfritz (1976) and Gupta and
  Levin (1976) studied residual and separating properties of these groups, per a web
  search; neither paper was read, and either may settle it.
- One route: if `C_r` is residually nilpotent, it is residually finite, since its
  lower-central quotients are finitely generated nilpotent. A caution: `H_r` lies in
  `γ_5(C_r)`. Indeed `C_r/γ_5(C_r) = F/γ_5(F)`, because
  `[F'', F] ⊆ γ_5(F)`, and that group is torsion-free. So any separating quotient must
  have nilpotency class at least 5.
- Rank 3 is not covered: the abstract speaks only of `n >= 4`. The rank-2 argument of
  `free-centre-by-metabelian-rank-two-linearity-proof` may extend to rank 3, but
  injectivity of the corner map was not checked there.
