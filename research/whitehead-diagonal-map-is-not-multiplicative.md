---
rg: 2
id: whitehead-diagonal-map-is-not-multiplicative
kind: claim
title: The Whitehead diagonal map X to diag(X, X^-1) is multiplicative only on commuting pairs
invalidates:
  - char-p-linear-embedding-projective-leavitt-power-proof
distinct_from:
  char-p-linear-groups-embed-in-projective-leavitt-power-e-groups: that is the embedding theorem whose proof used this map as a group embedding into E_m; this records that the map is not a homomorphism on any nonabelian group, so that proof does not land H in E_m.
---

**ESTABLISHED.** Let `R` be a ring and `X, Y in GL_N(R)`. Put
`w(X) = diag(X, X^-1)` in `GL_(2N)(R)`. Then `w(XY) = w(X) w(Y)` if and only
if `XY = YX`.

So for a nonabelian subgroup `H <= GL_N(R)`, the map `X |-> diag(X, X^-1, 1, ..., 1)`
is not a group homomorphism, and it embeds no nonabelian `H` as a subgroup.

**Consequence (bh-reviewer, 2026-09-12).** Theorem C of
`research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md` calls this map
"an injective homomorphism `H -> E_m(R_d)`". That step fails for every
nonabelian finitely generated linear group, for example `SL_3(F_p[t])`. So the
route `char-p-linear-embedding-projective-leavitt-power-proof` does not prove
its target. Its other steps stand:
- Lemma A: `H <= GL_N(R_d)`;
- Lemma B: each single `diag(X, X^-1)` lies in `E_(2N)(R_d)`;
- the centre calculation.
What is missing is a homomorphic embedding into `E_m`. The known candidates
need `K_1`-type information; see `## Attempts` on
`char-p-linear-groups-embed-in-projective-leavitt-power-e-groups`.
