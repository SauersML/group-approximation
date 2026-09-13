---
rg: 2
id: grigorchuk-hnn-extension-is-fp-infinity
kind: claim
title: Grigorchuk's finitely presented amenable HNN extension of the first Grigorchuk group is of type FP_infinity
distinct_from:
  grigorchuk-hnn-extension-is-fp-amenable-non-ea: that records finite presentation, amenability and non-elementary amenability; this asks for the higher finiteness property FP_infinity, which with finite presentation gives F_infinity.
---

**OPEN.** Grigorchuk's finitely presented HNN extension `𝔊^` of the first
Grigorchuk group (`grigorchuk-hnn-extension-is-fp-amenable-non-ea`) is of type
`FP_∞` over `Z`. Since `𝔊^` is finitely presented, this is equivalent to type
`F_∞`. Together with the import it would answer Zaremsky 1.12 through
`f-infinity-amenable-non-ea-via-grigorchuk-hnn`.

## Attempts

- **Alexander-module test (necessary condition; not yet evaluated).** Let `N`
  be the kernel of the map `𝔊^ → Z` that sends the stable letter to `1`. For
  an ascending extension along an injective endomorphism `σ`, `N` is the
  directed union of the conjugates `t^(−k) 𝔊 t^k`, so `H_k(N; F_2)` is the
  colimit of `H_k(𝔊; F_2)` under `σ_*`. By Shapiro's lemma
  `H_k(N; F_2) ≅ H_k(𝔊^; F_2[𝔊^/N])`. So if `𝔊^` is of type `FP_n` over `F_2`,
  then `H_k(N; F_2)` is finitely generated over the Noetherian ring
  `F_2[t, t^(−1)]` for all `k ≤ n`. The Schur multiplier `H_2(𝔊; Z)` is an
  infinite elementary abelian 2-group, as recalled in the Bartholdi–
  Grigorchuk–Šunić survey (arXiv:math/0510294). If `σ_*` acts on a basis by
  shifting finitely many relator families, the colimit is free of finite rank
  over `F_2[t, t^(−1)]`, consistent with `FP_2`. `FP_3` needs the same
  finiteness for `colim_σ H_3(𝔊; F_2)`. This lane knows no computation of
  `H_3(𝔊)`.
- **Kropholler fence (strategy constraint).** `𝔊` is an infinite, finitely
  generated, residually finite 2-group, so by Zelmanov its exponent is
  unbounded and `𝔊^` has finite subgroups of unbounded order. Kropholler's
  theorem for `LH𝔉`-groups (arXiv:1208.1008, Theorem 2.7(vii), under 0-finitary
  complete cohomology; for `FP_∞` groups, Kropholler 1993) then forces
  `𝔊^ ∉ LH𝔉` whenever `𝔊^` is `FP_∞`. `𝔊^` acts on its Bass–Serre tree with
  stabilizers conjugate to `𝔊`, so `𝔊 ∈ H𝔉` would put `𝔊^` in `H𝔉`. Hence
  `FP_∞` requires `𝔊 ∉ H𝔉`, and cannot be proved by Brown's criterion on a
  finite-dimensional contractible complex with `H𝔉` stabilizers.
- **No positive tool.** Brown's criterion on the Bass–Serre tree fails at the
  start, since the vertex stabilizers `𝔊` are not finitely presented.
