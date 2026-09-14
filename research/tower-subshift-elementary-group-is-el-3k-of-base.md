---
rg: 2
id: tower-subshift-elementary-group-is-el-3k-of-base
kind: claim
title: The k-level tower over an infinite minimal subshift is again one, and its elementary group EL_3 is EL_3k over the base subshift algebra
distinct_from:
  period-doubling-subshift-algebra-is-its-own-matrix-ring: that is the self-similarity A ≅ M_2(A) of the period-doubling shift; this is the general tower identity R_(X^(k)) ≅ M_k(R_X) for every infinite minimal subshift and every k.
  subshift-elementary-group-isomorphism-forces-orbit-equivalence: that asks whether S_X determines X; this records which rank changes the family of groups S_X already realizes, a calibration for that question.
---

**ESTABLISHED.** Let `(X,T)` be an infinite minimal subshift, `k ≥ 1`, `q` a prime power, and
`R_X = LC(X,F_q) ⋊_T Z`. Let `X^(k) = X × {0,…,k−1}`, with `S(x,i) = (x,i+1)` for `i < k−1` and
`S(x,k−1) = (Tx,0)`.

1. `(X^(k), S)` is conjugate to an infinite minimal subshift.
2. `R_(X^(k)) ≅ M_k(R_X)` as unital rings.
3. For every unital ring `R` and `n ≥ 2`, `EL_n(M_k(R)) = EL_(nk)(R)` inside `GL_(nk)(R)`.

So `EL_3(R_(X^(k))) ≅ EL_(3k)(R_X)`, and the same holds after dividing by centres.

**Consequences.**
- The family `S_X = EL_3(R_X)/Z`, over all infinite minimal subshifts `X`, contains `EL_(3k)(R_X)/Z`
  for every `X` and `k`.
- A rigidity statement for the family has to allow `S_(X^(k)) ≅ EL_(3k)(R_X)/Z`.
- For the period-doubling shift `X^(2) ≅ X`, because decimation conjugates the induced system on the
  even phase onto `X` (`period-doubling-subshift-algebra-is-its-own-matrix-ring`). So there
  `EL_3(R_X) ≅ EL_6(R_X)`.

Proof: route `tower-subshift-elementary-group-is-el-3k-of-base-proof`.

**Review (sk-verify-3, 2026-09-13): PASS (items 1–3).** Tower coding, matrix units p_i u^(i−j) with base corner via the universal property, and EL_n(M_k(R)) = EL_(nk)(R) re-derived. The period-doubling consequence rests on a node this route does not require and is not reviewed here. See `research/artifacts/sk-review-3-2026-09-13-part2.md` §5.
