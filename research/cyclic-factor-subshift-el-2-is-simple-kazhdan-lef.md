---
rg: 2
id: cyclic-factor-subshift-el-2-is-simple-kazhdan-lef
kind: claim
title: If an infinite minimal subshift has a clopen U with X = U ⊔ TU ⊔ … ⊔ T^(m−1)U, m ≥ 2, then EL_2 over its algebra is EL_2m over the induced system, simple and Kazhdan mod centre
distinct_from:
  tower-subshift-elementary-group-is-el-3k-of-base: that builds towers X^(k) over a given base and computes EL_3 of their algebras; this starts from a subshift with a finite cyclic factor, writes it as such a tower, and concludes that n = 2 already gives simple Kazhdan groups there, so n ≥ 3 is not a necessary hypothesis for every X.
  el-2-over-every-minimal-subshift-algebra-is-kazhdan: that is the open question for every infinite minimal subshift, e.g. Sturmian ones with no finite cyclic factor; this is the proved cyclic-factor case.
---

**ESTABLISHED (unreviewed)** by `cyclic-factor-subshift-el-2-is-simple-kazhdan-lef-proof`.

**Statement.** Let `(X,T)` be an infinite minimal subshift, `q` a prime power, `R_X = LC(X,F_q) ⋊_T Z`, `m ≥ 2`, and `U ⊆ X` clopen with `T^m U = U` and `X = U ⊔ TU ⊔ … ⊔ T^(m−1)U`. Put `Y = (U, T^m|_U)`. Then:
1. `Y` is conjugate to an infinite minimal subshift, and `X ≅ Y^(m)` (the height-`m` tower).
2. `R_X ≅ M_m(R_Y)` and `EL_2(R_X) = EL_(2m)(R_Y)`.
3. `EL_2(R_X)/Z` is an infinite finitely generated simple group with property (T).
4. For `q = 2`, `EL_2(R_X)` is LEF, since `R_Y` is a LEF ring.

**Examples.** Toeplitz subshifts and the period-doubling subshift, which factor onto `Z/2`.
**Non-example.** Sturmian subshifts have no finite cyclic factor: their eigenvalues other than `1` are irrational rotations.

**Use for the note.** A remark that "n = 2 loses (T)" would be false for these `X`. The note's `n = 3` is the range of Ershov–Jaikin-Zapirain and works for every `X`. Whether `n = 2` works for every `X` is `el-2-over-every-minimal-subshift-algebra-is-kazhdan`.

**Review (sk-verify-5, 2026-09-13): PASS.** Re-derived:
- The induced system `(U, T^m)` is minimal, infinite and expansive, hence a subshift.
- The matrix units `u^i e_U u^(-j)` give `R_X ≅ M_m(e_U R_X e_U)`, with corner `LC(U,F_q) ⋊_(T^m) Z`, since `e_U u^j e_U = 0` unless `m | j`.
- `EL_2(M_m(S)) = EL_(2m)(S)`: a transvection inside one block is `[t_xy, t_yz] = t_xz`, with `y` in the other block.
- (T) for `EL_(2m)` needs only `2m ≥ 3`.
- Simplicity comes from the Steinberg criterion; LEF over `F_2` from the LEF ring `R_Y`.

The input `tower-subshift-elementary-group-is-el-3k-of-base` is PASS for items 1–3 (sk-verify-3, part 2 §5). See `research/artifacts/sk-review-5-2026-09-13-part1.md` §3.
