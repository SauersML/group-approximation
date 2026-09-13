---
rg: 2
id: sp4-fp-regular-principal-series-irreducible
kind: claim
title: Regular principal series of Sp_4(F_p) are irreducible, with either central sign available
distinct_from:
  deligne-universal-cover-lattice-is-non-rf-kazhdan: that records property (T) and non-residual-finiteness of Deligne's lattice; this is a finite-group representation fact about Sp_4(F_p), used to build large irreducible representations of Sp_4(Z) with a chosen action of -I.
---

**OPEN (classical import; two ingredients not re-read at source).**

Let `p >= 11` be prime. Let `V = F_p^4` have basis `e_1, e_2, f_2, f_1` with
`omega(e_i, f_i) = 1`, and let `G_p = Sp_4(F_p)`. Let `B_p` be the stabilizer of
the flag `<e_1> ⊂ <e_1, e_2>`, so `B_p` is upper triangular in this basis, with
torus `T_p = {diag(a, b, b^-1, a^-1)} ≅ (F_p^x)^2` and unipotent radical `U_p`.
A character `theta = (alpha, beta)` of `T_p` extends to `B_p` through
`B_p -> B_p/U_p ≅ T_p`.

1. If the eight characters `(alpha^±1, beta^±1)` and `(beta^±1, alpha^±1)` are
   pairwise distinct (`theta` regular), then `Ind_(B_p)^(G_p) theta` is
   irreducible of degree `[G_p : B_p] = (p+1)^2 (p^2+1)`.
2. `-I` lies in `T_p` and is central. It acts on `Ind theta` by the scalar
   `theta(-I) = alpha(-1) beta(-1)`.
3. Let `psi` generate the character group of `F_p^x`, so `psi(-1) = -1`. Then
   `theta^- = (psi, psi^2)` and `theta^+ = (psi, psi^3)` are regular, with
   `theta^-(-I) = -1` and `theta^+(-I) = +1`.

## Status of the parts

- **(2)** For `f` in the induced module and `t = -I` central in `G_p`, the
  translate by `t` equals the translate by `t` on the other side, and `t ∈ B_p`,
  so `t` acts by `theta(t)`.
- **(3)** Regularity means `alpha^2 ≠ 1`, `beta^2 ≠ 1` and `alpha ≠ beta^±1`.
  - For `theta^-`: `psi^2`, `psi^4` and `psi^3` are nontrivial because `p - 1`
    divides none of 2, 3, 4. Also `psi ≠ psi^2`.
  - For `theta^+`: `psi^2`, `psi^4` and `psi^6` are nontrivial because `p - 1`
    divides none of 2, 4, 6 when `p >= 11`. Also `psi ≠ psi^3` and
    `psi ≠ psi^-3`.
  - Signs: `theta^-(-I) = (-1)(-1)^2 = -1` and `theta^+(-I) = (-1)(-1)^3 = +1`.
- **(1)** This is the classical irreducibility of principal series in general
  position (Harish-Chandra). For `Sp(4,q)` see B. Srinivasan, *The characters of
  the finite symplectic group Sp(4,q)*, Trans. AMS 131 (1968), 488–525; that
  paper was **not** re-read here. Proof sketch:
  - Mackey's intertwining formula gives
    `dim End_G(Ind theta) = sum over w in B\G/B of dim Hom_(B ∩ wBw^-1)(theta, theta^w)`.
  - The Bruhat decomposition `G_p = ⊔_(w in W) B_p w' B_p` has representatives
    `w'` in `N(T_p)`, where `W` is dihedral of order 8. So `T_p ⊂ B_p ∩ w'B_pw'^-1`,
    and on `T_p` the character `theta^(w')` is `w · theta`.
  - For regular `theta` only `w = 1` contributes, so the endomorphism ring is
    one-dimensional.
  - Neither the Bruhat decomposition for `Sp_4(F_p)` nor the intertwining form of
    Mackey's formula was checked against a source in this landing. The
    character form of Mackey's formula was checked; it is quoted in
    `sp4-regular-trace-asymptotic-reps-need-not-round-proof`.

Consumer: `sp4-regular-trace-asymptotic-reps-need-not-round-proof`.
