---
rg: 2
id: root-localization-commutator-is-never-scalar
kind: claim
title: In root detection over a subshift crossed product, the localized commutator fixes the extreme tower levels, so it is never a nonidentity scalar
distinct_from:
  subshift-elementary-group-is-simple-modulo-centre: that is the simplicity theorem, whose written proof splits root detection into a non-scalar case and a scalar case; this lemma shows the scalar case never occurs, so the non-scalar case alone proves it.
artifacts:
  - research/artifacts/sk-coefficients-proposal-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `root-localization-commutator-is-never-scalar-proof`.

**Setting.**
- X is an infinite minimal subshift and `R = LC(X,F_q) ⋊_T Z`, with `u f u^{-1} = f∘T^{-1}`.
- `E_ab(W) = χ_{T^aW} u^{a-b}`.
- `n ≥ 2`, `w ≥ 0`, `m = w+1`. U is clopen with `U ∩ T^jU = ∅` for `0 < |j| ≤ 2m`, so
  `B_m(U) = span{E_ab(W) : |a|,|b| ≤ m, W ⊆ U clopen} ≅ M_{2m+1}(LC(U,F_q))`.
- `g ∈ GL_n(R)`, and every entry of `g` and `g^{-1}` involves only powers `u^j` with `|j| ≤ w`.
- `s = λ E_{a0}(W)` with `|a| ≤ 1`, `λ ∈ F_q`, `W ⊆ U` clopen. This covers `λχ_C = λE_00(C)`, `χ_C u = E_10(T^{-1}C)` and `χ_C u^{-1} = E_{-1,0}(TC)`.
- `h = e_ij(s)` with `i ≠ j`, and `k = g h g^{-1} h^{-1}`.

**Statement.**
1. Every entry of `k − I` lies in `span{E_ab(W') : |a| ≤ m, |b| ≤ w, W' ⊆ U}`.
2. Let `e` be the unit of `B_m(U)`, so `k = (1−e)I + eke`. Under `M_n(B_m(U)) ≅ LC(U, M_d(F_q))`, `d = n(2m+1)`, `k` gives a locally constant `κ: U → GL_d(F_q)`. Then `κ(x)` fixes the 2n basis vectors at the levels `b = ±m`, for every `x ∈ U`.
3. In particular `κ(x)` is scalar only when `κ(x) = I`.

**Use.**
- In root detection for `EL_n(LC(X,F_q) ⋊ Z)`, `κ ≢ I` always has a non-scalar value. So the case "κ is a nonidentity scalar" never occurs: b965d63ba `thm:root` Case 2, and write-up part 2 §6.2(d), `research/artifacts/pestov-9-1-writeup-2026-09-13-part2.md`.
- Over F_q the finite simple group step then only needs that `SL_d(F_q)` is perfect with simple central quotient.
- Over F_2 the lemma is not needed, since `GL_d(F_2)` is centreless.
