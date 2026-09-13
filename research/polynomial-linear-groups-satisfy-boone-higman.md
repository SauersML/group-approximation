---
rg: 2
id: polynomial-linear-groups-satisfy-boone-higman
kind: claim
title: Every subgroup of GL_N(Z[1/m][t_1..t_k]) embeds in a finitely presented simple group
distinct_from:
  rational-linear-groups-satisfy-boone-higman: that is Zaremsky's GL_n(Q) theorem, the case k = 0; this adds polynomial coordinates of every transcendence degree through parameter-coordinate hosts.
  algebraic-linear-groups-satisfy-boone-higman: that is the transcendence-degree-zero class through restriction of scalars; this is linear groups over polynomial rings Z[1/m][t_1..t_k], including SL_3(Z[t]).
  char-zero-linear-groups-satisfy-boone-higman: that is the full characteristic-zero class, which this claim settles only together with the change of coordinates char-zero-linear-groups-embed-in-polynomial-s-integer-groups; this is the case where polynomial coordinates are given.
  positive-char-surface-linear-groups-satisfy-boone-higman: that is a positive-characteristic class reached through Leavitt tensor hosts; this is characteristic zero through self-similar affine hosts.
  el3-z-t-embeds-in-no-host-with-number-field-local-groups: that excludes eventually similar hosts whose local groups are linear over number fields; the host here has local group Z[t]^n x| E_n(Z[t]), which is not linear over a number field.
artifacts:
  - research/artifacts/bh-sl3-zt-host-2026-09-12.md
---

**ESTABLISHED (2026-09-12)** through
`polynomial-linear-groups-satisfy-boone-higman-via-zaremsky`. ~~Not independently
reviewed; see the imports of `elementary-groups-over-polynomial-s-integers-are-fp`.~~
*Reviewed (lane `bh-poly-linear-review`, 2026-09-12).* The status stands. The
review corrected the embedding step of the route and two citations in the proof
of `elementary-groups-over-polynomial-s-integers-are-fp`.

**Statement.** Let `m >= 1`, `k >= 0`, `R = Z[1/m][t_1,...,t_k]` and `N >= 1`.
Every subgroup of `GL_N(R)` embeds in a finitely presented simple group.

**Consequences.**
- Every finitely generated subgroup of `GL_N(Q[t_1,...,t_k])` embeds in a finitely
  presented simple group. The entries of its generators and of their inverses lie
  in some `Z[1/m][t_1..t_k]`.
- In particular `SL_3(Z[t])` embeds in a finitely presented simple group. So does
  every `GL_N(Z[t_1..t_k])`.
- The same holds for `GL_N(S)` whenever `S ⊇ R` is commutative and finitely
  generated projective as an `R`-module.
  - Choose `Q` with `S^N ⊕ Q ≅ R^M`. Then `g -> g ⊕ 1_Q` embeds `GL_N(S)` in
    `GL_M(R)`.
  - Example: `Z[1/m][x,y]/(y^2 - x^3 - x)`, which is free over `Z[1/m][x]`.

**The host.**
- Let `n = max(k+4, 2N)` and let `p` be a prime not dividing `m`.
- ~~The input embeds by `g -> diag(g, g^-1)` in `E_(2N)(R) <= E_n(R)`, and so in
  `G = R^n x| E_n(R)`.~~ *Corrected (review, 2026-09-12):* `g -> diag(g, g^-1)` is
  not a homomorphism.
  - The input embeds by `g -> diag(g, (g^T)^-1, I_(n-2N))` in `SL_n(R)`.
  - `SL_n(R) = E_n(R)`, because `n >= k+3` lies in Vaserstein's stable range and
    `SK_1(R) = 0`.
  - So the input embeds in `G = R^n x| E_n(R)`.
- `G` is finitely presented and self-similar on `Z_p^n x Z_p^k`.
- The simple group is the commutator subgroup of a Röver–Nekrashevych group of `G`,
  as in Zaremsky's theorem.

**Beyond polynomial coordinates** (2026-09-12, lane `bh-char0-linear-reduction`).
- **Not covered by this host directly:**
  - Laurent coordinates, such as `SL_3(Z[t^(+-1)])`;
  - denominators that are non-constant polynomials in the `t_j`.
- **Reached by changing coordinates first.**
  `char-zero-linear-groups-embed-in-polynomial-s-integer-groups` puts every
  finitely generated characteristic-zero linear group in some
  `GL_M(Z[1/m][s_1..s_k])`. For example, `SL_3(Z[t^(+-1)]) <= SL_6(Z[s])` with
  `s = t + t^-1`.
- **Consequence.** Route `char-zero-linear-bh-via-polynomial-s-integer-hosts`
  then settles `char-zero-linear-groups-satisfy-boone-higman`, resting on this
  claim.
