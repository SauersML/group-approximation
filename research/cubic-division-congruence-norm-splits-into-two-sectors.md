---
rg: 2
id: cubic-division-congruence-norm-splits-into-two-sectors
kind: claim
title: The prime-level congruence norm of SL_1(O_D) is the maximum of a vector-sector norm and a Gelfand--Graev-sector norm, and the Gelfand--Graev Ihara traces count unipotent reductions
distinct_from:
  cubic-division-ihara-traces-count-roots-mod-p: that computes Ihara traces inside the degenerate principal series only; this shows that the degenerate series and the Gelfand--Graev representations together exhaust l^2_0(SL_3(F_p)), and computes the traces of the complementary generic sector.
---

ESTABLISHED (unreviewed; one import, the multiplicity one of the Gelfand--Graev representation of
`GL_3(F_p)`).  Let `D`, `Gamma_D`, `P_D` and `pi_p = l^2_0(SL_3(F_p))` be as in
`cubic-division-congruence-representations-converge-strongly`.  Put:
- `G = SL_3(F_p)`, `U` its upper unitriangular subgroup, `kappa = gcd(3, p - 1)`, and `psi` a nontrivial
  additive character of `F_p`;
- `sigma_p^0 = l^2_0(F_p^3 minus 0)`;
- `GG_p` the sum, over representatives `a` of `F_p^x / F_p^x3`, of the Gelfand--Graev representations
  `Ind_U^G psi_a`, where `psi_a(u) = psi(u_12 + a u_23)`.  Its dimension is `d_p = kappa (p^2 - 1)(p^3 - 1) <= 3 p^5`.

1. **Two sectors.**  Every nontrivial irreducible representation of `G` is a constituent of exactly one
   of `sigma_p^0` and `GG_p`.  Hence, for `p` not in `P_D` and every `z in C[Gamma_D]`,
   `||pi_p(z)|| = max(||sigma_p^0(z)||, ||GG_p(z)||)`.
2. **Equivalence.**  Both sectors converge in distribution to `lambda_(Gamma_D)` along primes.  So
   `pi_p -> lambda` strongly iff `sigma_p^0 -> lambda` strongly and `GG_p -> lambda` strongly.
3. **Gelfand--Graev character.**  For `g in G`,
   `chi_(GG_p)(g) = kappa [(p^2 - 1)(p^3 - 1) 1{g = 1} - (p^2 - 1) 1{rank(g - 1) = 1} + 1{g unipotent, rank(g - 1) = 2}]`.
4. **Traces for a free pair.**  Let `A, B in Gamma_D` generate a free group `H`, put
   `Z = A + A^-1 + B + B^-1`, and let `p` lie outside `P_D` and `P_H`.  Let `CR_n` be the cyclically
   reduced words of length `n`, and define

   ```text
   I_p(n)  = #{ w in CR_n : w == 1 mod p }
   Tr_p(n) = #{ w in CR_n : rank(w - 1 mod p) = 1 }
   R_p(n)  = #{ w in CR_n : Trd(w) == Trd(w^-1) == 3 mod p,  rank(w - 1 mod p) = 2 }
   ```

   Then `T_GG(n) = sum_(w in CR_n) chi_(GG_p)(w) = kappa [(p^2 - 1)(p^3 - 1) I_p(n) - (p^2 - 1) Tr_p(n) + R_p(n)]`.
   By `free-group-ihara-bass-outlier-trace-criterion` with `q = 3`:
   - (a) If `limsup_p ||GG_p(Z)|| <= 2 sqrt 3`, then for every `delta > 0`, all large `p` and all `n`,
     `|T_GG(n) - d_p (1 + (-1)^n)| <= 2 d_p (sqrt 3 + delta)^n`.
   - (b) Conversely, suppose `T_GG(n_p) - 2 d_p <= p^C (sqrt 3 + delta_p)^(n_p)` at even `n_p` with
     `n_p / log p -> infinity` and `delta_p -> 0`.  Then `limsup_p ||GG_p(Z)|| <= 2 sqrt 3`.

   Under exact equidistribution of `CR_n` in `G`, the three weighted counts are of size `3^n / p^2` and
   cancel exactly.  For fixed `n` and large `p`, `T_GG(n) = 0`.  So the Gelfand--Graev sector has no
   vertical Chebotarev statistics; its content sits entirely at `n >> log p`.

**Scope.**  This is a structural reduction, not progress on the upper bound.
- Part 1 means the target needs no separate treatment of cuspidal, Steinberg or principal-series
  sectors.  Everything outside the Schreier graphs on nonzero vectors mod `p` is one monomial
  representation on `G/U`.
- In that sector the Ihara traces see only the words whose reduction mod `p` is unipotent, that is, the
  simultaneous divisibility `p | Trd(w) - 3`, `p | Trd(w^-1) - 3`.  The vector sector sees
  `p | Trd(w^-1) - Trd(w)`.

**Numerics** (`research/artifacts/cubic-division-congruence-norm-splits-2026-09-16.md`, Section 6).
- Part 3 was checked exactly at `p = 5, 7, 11, 13` on an explicit model of `G/U`.
- At `p = 13`, for the certified pair `a^19, b^19`, the extreme Ritz values are 3.4772 in every
  Gelfand--Graev sector and 3.5416 in the vector sector.  Both lie inside the ranges of random controls.
  This is evidence only.

Proof: `cubic-division-congruence-norm-splits-into-two-sectors-proof`.
