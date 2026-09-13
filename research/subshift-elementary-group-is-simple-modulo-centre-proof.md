---
rg: 2
id: subshift-elementary-group-is-simple-modulo-centre-proof
kind: route
title: Localize a commutator into a tower matrix ring, detect a root there, and spread it by the level ideal
target: subshift-elementary-group-is-simple-modulo-centre
requires: [minimal-subshift-algebra-is-simple-lef-ring]
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
---

Complete derivation in the artifact, Part 1, §1.5--1.6 and §4.

1. **Level ideal.** `I(N) = {a : e_12(a) ∈ N}` is a two-sided ideal. It uses
   `[e_12(a), e_23(b)] = e_13(ab)`, `[e_31(b), e_12(a)] = e_32(ba)`, and signed permutation matrices,
   which lie in `EL_3`. `R` is simple, so `I(N) != 0` forces `N = G`.
2. **Localized noncommuting root.** Let `g ∈ N` be noncentral, `w` the propagation bound of `g` and
   `g^(-1)`, and `L = 2w+3`. The set of `s` with `g` commuting with every `e_ij(s)` is a subring,
   since `e_ij(st) = [e_ik(s), e_kj(t)]`. The elements `λ chi_C` and `λ chi_C u^(±1)`, for
   `λ ∈ F_q` and cylinders `C` with return times `> L`, generate `R` and lie in `B_1(U)`. The scalars
   `λ` are needed when `q` is not prime (review note, 0efeac410). So some such `h = e_ij(s)` fails to
   commute with `g`.
3. **Absorption.** `k = [g,h] ∈ N`, `k != 1`, and `k - I ∈ M_3(B_(1+w)(U)) ≅ LC(U, M_d(F_q))`. This
   holds because `(f u^i) E_ab(W) (f' u^j)` is a combination of `E_(a+i, b-j)(W_k)`.
4. **Noncentral value.** If `κ(x_0)` is not scalar, `ι_W : SL_d(F_q) -> G` over a piece `W`
   lands in `G`:
   - off-diagonal transvections are roots;
   - same-row transvections satisfy `I + x E_pp = [e_pp''(x), e_p''p(y)]`, where `x = c E_ab(W)`,
     `y = E_bb(W)`, `xy = x`, `yx = 0`, `x^2 = 0`.

   `ι_W^(-1)(N)` contains `[κ_0, ε]` for all `ε`. If it were central, `κ_0` would centralize the
   perfect group `SL_d(F_q)`, i.e. be scalar. So it is all of `SL_d(F_q)`, `d >= 9`, and
   `e_12(chi_W) ∈ N`.
5. **Scalar value.** Then `k = c I_3` with `c ∈ LC(X)^x` equal to `λ_0 != 1` on the tower over `W`
   and `1` outside the tower. With `r = chi_(T^(m'+1) W) u != 0`,
   `[k, e_12(r)] = e_12((λ_0^(-1) - 1) r) ∈ N`.
6. **Centre and finite quotients.** Commuting with all roots forces `cI_3`, `c ∈ Z(R) = F_q`. A
   finite-index normal subgroup cannot lie in the finite centre of an infinite group.
