---
rg: 2
id: msz-guarded-projection-recurrence-is-relation-r6
kind: claim
title: The guarded projection recurrence is relation (R6) of the MSZ machine algebra and is retained verbatim by Fanizza et al.
distinct_from:
  msz-clifford-machine-skeleton-has-polynomial-fillings: that imports the finitely generated group skeleton, its commutator schedule and its polynomial word problem; this imports the one nonlinear star-polynomial relation of the machine *algebra* and its Boolean form in the Fanizza BCS.
  fanizza-pauli-guard-switches-off-at-the-terminal-cell: that evaluates the guarded relation in the exact HALT model and proves the guard is the halting switch; this only records, with source locations, that the relation is a defining relation of both algebras.
---

**Literature import (verified 2026-08-22 against arXiv:2312.05617v2 and
arXiv:2510.04943v4).**

1. In Mehta--Slofstra--Zhao, the algebra `A_L(m)` is presented on the
   generators `X_H cup X_0` (the machine-group generators together with
   `U_1, U_2, P, Q, X_tilde, Z_tilde`) by relations (R0)--(R6), displayed
   immediately after Lemma 4.6 and the presentation of `G_L`: (R0) every
   generator is an order-two unitary, (R1) the relations of `H_L`, (R2)
   `U` and `Q` commute with `X, Z, S, T, J`, (R3) `X_tilde Q = X_(m,0) Q`
   and `Z_tilde Q = Z_(m,0) Q`, (R4) `U X_tilde U^* = S X_tilde S^*` and
   `U Z_tilde U^* = T Z_tilde T^*`, (R5) `[P, Q] = 0`, and

   ```text
   (R6)  (P + X_tilde P X_tilde - U P U^*)
         (1 + J X_tilde Z_tilde X_tilde Z_tilde) = 0.             (MGR1)
   ```

   This is the only nonlinear relation of the presentation (Remark 4.9:
   every relator has norm at most `6` in the free product algebra and the
   number of relations is independent of `m`).

2. In the presentation of the machine group `G_L` (same section), relation
   (2) is the addressed commutator schedule

   ```text
   [X_(m,i), Z_(m,i)] = J   if  i + 1 != 0  (mod h(m) + 1),
   [X_(m,i), Z_(m,i)] = 1   if  i + 1  = 0  (mod h(m) + 1),      (MGR2)
   ```

   with `J` central of order two; so the Pauli identity
   `X Z X Z = J` holds on every addressed cell except the terminal one,
   where the two involutions commute.

3. In the completeness representation of Lemma 4.10 (halting time
   `n = h(m)`), `P` is represented by `sum_i pi(P_i) (x) E_(i,i)` with

   ```text
   P_i = ((1 - J)/2) ((1 - Z_(m,i))/2) ... ((1 - Z_(m,n-1))/2)  (i < n),
   P_n = (1 - J)/2,                                              (MGR3)
   ```

   so `((1 + J)/2) P_i = 0` for every `i`; on the preterminal cells
   `1 + J X Z X Z = 2` and the unguarded recurrence
   `P_i + X P_i X = P_(i+1)` is checked directly, while on the terminal
   cell `X Z X Z = 1` and the factor `1 + J` annihilates every `P_i`, which
   is how `(MGR1)` is verified there.

4. Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao retain the
   relation unchanged: their nested BCS has relation groups
   `(R~2)--(R~6)`, where `(R~5)` is `[P, Q] = 0` together with `D = PQ`
   (the Boolean constraint `C_17 : O_D = O_P AND O_Q`), and `(R~6)` is
   exactly `(MGR1)` together with the statement that
   `P, X_tilde P X_tilde, U P U^*, J, X_tilde Z_tilde X_tilde, Z_tilde`
   mutually commute -- the six-variable Boolean constraint `C_18` of
   Proposition 5.13.  Their proof of Proposition 5.13 reuses the Lemma 4.10
   representation.

Consequently the guarded product is a defining relation of both machine
algebras, `(FTG2)` of `fanizza-pauli-guard-switches-off-at-the-terminal-cell`
and `(CDS2)` of `constant-depth-schur-lift-of-doubling-tape` are the same
cited relation, and the terminal switch used there is `(MGR2)`--`(MGR3)`.
