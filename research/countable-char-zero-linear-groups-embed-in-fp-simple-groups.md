---
rg: 2
id: countable-char-zero-linear-groups-embed-in-fp-simple-groups
kind: claim
title: Every countable linear group over a field of characteristic zero embeds in a finitely presented simple group
distinct_from:
  char-zero-linear-groups-satisfy-boone-higman: that is the finitely generated subgroups, which is established; this is every countable subgroup, finitely generated or not.
  gl-n-q-embeds-in-fp-simple-group: that is the single countable group GL_n(Q), which this claim implies.
  gl-n-qbar-embeds-in-fp-simple-group: that is GL_n(Qbar), which this claim implies.
artifacts:
  - research/artifacts/gq-gq-transfer-consequences.md
---

**OPEN.** For every `n >= 1` and every field `K` of characteristic 0, every
countable subgroup of `GL_n(K)` embeds in a finitely presented simple group.

**Equivalent form.** Let `Ω` be an algebraic closure of `Q(t_1, t_2, ...)`. The
claim holds if and only if `GL_n(Ω)` embeds in a finitely presented simple group
for every `n`. For the nontrivial direction:
- the entries of a countable subgroup of `GL_n(K)` generate a countable subfield
  `K_0` of transcendence degree at most `ℵ_0`;
- a transcendence basis of `K_0` maps into `{t_i}`, and the algebraic part then
  embeds into the algebraically closed `Ω`;
- so the subgroup lies in `GL_n(Ω)`.

**Position.**
- It implies `gl-n-q-embeds-in-fp-simple-group`,
  `number-field-gl-n-embeds-in-fp-simple-group` and
  `gl-n-qbar-embeds-in-fp-simple-group`.
- The finitely generated case is established
  (`char-zero-linear-groups-satisfy-boone-higman`).
- The Boone–Higman conjecture implies it through survey Corollary 3.5.
  `GL_n(Ω)` has solvable word problem for a computable enumeration: `Q(t_1, ...)`
  is a computable field, and it has a computable algebraic closure (Rabin 1960).
  The countable-input form of the conjecture is left to lane `gq-reform-countable`.
- Beyond number fields, `GL_n(Q)` does not suffice by restriction:
  - `GL_2(Q(t))` lies in no `GL_N(Q)`. The subgroup `(Q(t),+)` is divisible of
    infinite rank. A divisible abelian `D <= GL_N(Q)` is unipotent: eigenvalues of
    its elements have degree `<= N` and roots of every order of degree `<= N`, so by
    Northcott and Kronecker they are roots of unity, of bounded order. The
    semisimple parts then form a divisible group of bounded exponent, which is
    trivial. Finally `log` embeds a unipotent abelian group additively in
    `M_N(Q)`, so its rank is at most `N^2`;
  - `GL_n(Qbar)` lies in no `GL_∞` over a number field
    (`prufer-groups-do-not-embed-in-gl-infinity-q`).

## Attempts

None.
