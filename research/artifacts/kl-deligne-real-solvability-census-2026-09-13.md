# Real symplectic solvability census for Deligne Schur-certificates (2026-09-13)

Lane hl-kl-certificate-search. Target: `sp4-schur-kernel-meets-the-deligne-triple-class`.
Pruning theorem: `real-symplectic-solutions-kill-no-deligne-schur-class` (landed f9f20d5e2).
A nonsingular equation over `Sp_4(Z)` with a solution in `Sp_4(R)` kills no class
detected by Deligne's triple multiplier. So the census asks which short equations over
torsion-generated packets have real symplectic solutions.

## 1. Certificate format (what a witness must be)

A witness is a triple `(B, w, x)`:
- `B <= Sp_4(Z)` finitely generated, containing the coefficients of `w`;
- `w in B * <t>` nonsingular;
- `x in K_2(B, w)` with `alpha_H(iota_* x) != 0` in `Z/3`, where `alpha` is the
  multiplier of the connected three-fold cover of `Sp_4(R)` restricted to `Sp_4(Z)`.
Constraints already on main: `B` non-amenable, with torsion or a non-amenable reduced
t-shape, invisible to finite quotients, and `L_(alpha|B)(B)` not Connes-embeddable.
New constraint (RS2): `w(T) = 1` has no solution `T in Sp_4(R)`.

## 2. Packets and words

Torsion elements of `Sp_4(Z)`:
- `J = [[0, I], [-I, 0]]` (order 4);
- `D_k = diag(R_k, R_k^(-T))` with `R_3 = [[0,-1],[1,-1]]`, `R_4 = [[0,-1],[1,0]]`,
  `R_6 = [[1,-1],[1,0]]`;
- `P = diag(S, S)`, `S = [[0,1],[1,0]]` (order 2);
- conjugates by shears `U_M = [[I, M], [0, I]]`, `M_1 = [[1,0],[0,0]]`,
  `M_2 = [[1,1],[1,0]]`.

Packets `B = <a, b>`:

| packet | a | b |
|---|---|---|
| J_UJ1 | J | U_M1 J U_M1^-1 |
| J_UJ2 | J | U_M2 J U_M2^-1 |
| D3_UD6 | D_3 | U_M2 D_6 U_M2^-1 |
| D4_UJ2 | D_4 | U_M2 J U_M2^-1 |
| P_UD3 | P | U_M1 D_3 U_M1^-1 |

Words: `w = T^(e_1) g_1 ... T^(e_L) g_L`, exponent sum `+1`, one representative per
cyclic class of shapes, coefficients in `{a, b, a^-1, b^-1}`.
- L = 3: shape (-1, 1, 1), 4^3 = 64 words per packet, 320 in total.
- L = 5: shapes (-1, -1, 1, 1, 1) and (-1, 1, -1, 1, 1), 2 x 4^5 = 2048 words per packet, 10240 in total.

## 3. Method

- Numerical search (`sp4solve.py`): minimize `||w(T) - I||_F` over `T = exp(X_1) exp(X_2)`,
  `X_i in sp_4(R)`, Levenberg–Marquardt with random restarts.
- Calibration:
  - compact coefficients (`J`, `D_4` in `Sp_4(Z) cap U(2)`; Gerstenhaber–Rothaus
    guarantees solutions): 64 of 64 solved;
  - singular control `T J T^-1 D_3^-1` (orders 4 and 3, not conjugate): unsolved, as required.
- Certification (`certify.py`): Cayley chart `T = P cay(X)`, Newton refinement at 60 digits,
  Krawczyk test over mpmath interval arithmetic with forward-mode AD. Success certifies a
  unique exact zero, hence an exact `T in Sp_4(R)` with `w(T) = 1`.

## 4. Results

(filled in when the MSI jobs return)
