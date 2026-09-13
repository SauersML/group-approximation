---
rg: 2
id: laurent-sl3-real-cohomology-from-chamber-quotient
kind: claim
title: Congruence subgroups of SL_3(F_q[t,1/t]) act on the t-adic building with one chamber as quotient, so their real cohomology is a three-term complex of one-place H^2 groups
distinct_from:
  sl3-polynomial-congruence-subgroups-have-large-b2: that computes b_2 of congruence subgroups of the one-place group SL_3(F_q[t]) from the Soulé sector; this treats the two-place Laurent group, which acts on the t-adic building with one chamber as quotient and infinite cell stabilizers, and assembles its real cohomology from those one-place groups.
  harder-function-field-s-arithmetic-cohomology-vanishing: that is Harder's vanishing theorem for all S-arithmetic congruence subgroups; this is an elementary chamber spectral sequence for the Laurent SL_3, which with Harder's theorem becomes an exactness statement about one-place groups and a formula for the top Betti number.
---

**ESTABLISHED (unreviewed).** Items 1--2 use only property (T) and the equivariant spectral
sequence. Item 3 adds Harder's theorem. Item 4 is an independent check under hypothesis (S) of
`sl3-polynomial-congruence-subgroups-have-large-b2`.

**Setting.** `q` a prime power, `O_S = F_q[t,1/t]`, `A = SL_3(O_S)`. For `f ∈ F_q[t]` with
`f(0) ≠ 0`, `A(f) = ker(A -> SL_3(O_S/(f)))`, and `Γ(f) = A(f) ∩ SL_3(F_q[t])` is the principal
congruence subgroup of level `f` of `SL_3(F_q[t])`. `X_0` is the Bruhat--Tits building of
`SL_3(F_q((t)))` and `c` its standard chamber, with vertices `v_0 = [O_0^3]`,
`v_1 = [diag(t,1,1)O_0^3]` and `v_2 = [diag(t,t,1)O_0^3]`, where `O_0 = F_q[[t]]`.

1. **One chamber.** `A(f)` is dense in `SL_3(F_q((t)))`. It acts on `X_0` type-preservingly,
   with quotient the single chamber `c`.
   - The stabilizer of `v_i` is `g_iΓ(f)g_i^(-1)`, with `g_i ∈ {1, diag(t,1,1), diag(t,t,1)}`.
   - Every cell stabilizer contains the chamber stabilizer `A(f)_c ⊇ Γ(tf)`.
   - All cell stabilizers are infinite Kazhdan groups acting properly on the building of
     `SL_3(F_q((1/t)))`.

2. **Three-term complex.** Let `H^2_σ = H^2(A(f)_σ;R)`, and let `d^0, d^1` be alternating sums of
   restriction maps in

   ```text
   0 -> ⊕_i H^2_(v_i) --d^0--> ⊕_(edges e ⊂ c) H^2_e --d^1--> H^2_c -> 0.        (CH)
   ```

   Then

   ```text
   H^0(A(f);R) = R,   H^1 = 0,   H^2 = ker d^0,   H^3 = ker d^1/im d^0,   H^4 = coker d^1,   H^(>=5) = 0.
   ```

   In particular `H^2(A(f);R) -> H^2(Γ(f);R)` is injective.

3. **With Harder's theorem** (`harder-function-field-s-arithmetic-cohomology-vanishing`, with
   `r|S| = 4`).
   - `H^2(A(f);R) = H^3(A(f);R) = 0`, so (CH) is exact at its first two terms.
   - **Rigidity of one-place classes.** No nonzero family of real classes on the three vertex
     groups (each isomorphic to `Γ(f)`) agrees on the three edge groups. For `q = 2` and `f` of
     degree 2 with `f(0) ≠ 0`, the vertex group has `b_2(Γ(f)) ∈ {927, 1304}`, and no nonzero
     class of it extends compatibly.
   - **Top Betti number from one-place data.**

     ```text
     b_4(A(f)) = Σ_i b_2(A(f)_(v_i)) - Σ_e b_2(A(f)_e) + b_2(A(f)_c).
     ```

     By Harder's item 2 this is the multiplicity of the Steinberg representation of
     `SL_3(F_q((t))) × SL_3(F_q((1/t)))` in the discrete spectrum at level `A(f)`. Each term on the
     right is the top Betti number of a congruence subgroup of `SL_3(F_q[t])`.
     - The vertex groups are principal levels `Γ(f)`, which are in the table of
       `sl3-polynomial-congruence-subgroups-have-large-b2`.
     - The edge and chamber groups are parahoric-type levels between `Γ(tf)` and `Γ(f)`. The same
       Soulé-sector count covers them with double-coset counts in place of the orbit sizes
       `|SL_3(A)|/|π(Γ_σ)|`, but that table does not list them, and this count has not been done.
     *Wording correction (ex-verify2-dynamics, 2026-09-13).* The earlier text said the table
     "computes" all four terms.

4. **Independent check at `f = 1` (under (S)).** Every cell stabilizer of `A` contains
   `Γ(t)`, and `b_2(Γ(t)) = 0`. So `H^*(A;R) = R`, and `b_4(A) = 0`, without using Harder.

Derivation: `laurent-sl3-real-cohomology-from-chamber-quotient-proof`.

**Model tests.**
- *A real object where the vertex term is large.* `b_2(Γ(t^2)) = 927` at `q = 2`. Item 2 alone
  does not make `H^2(A(t^2+1);R)` vanish; Harder's theorem does.
- *Calibration.* At `f = 1` the only nonzero row of the spectral sequence is `q = 0`, the
  cochains of a simplex.
