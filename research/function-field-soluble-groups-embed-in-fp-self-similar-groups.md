---
rg: 2
id: function-field-soluble-groups-embed-in-fp-self-similar-groups
kind: claim
title: A finitely generated soluble linear group over a positive-characteristic field of transcendence degree at most one virtually lies in a finitely presented self-similar affine Borel group
distinct_from:
  positive-char-surface-linear-groups-satisfy-boone-higman: that embeds every finitely generated linear group of transcendence degree at most two in a Leavitt tensor unit group; this puts the soluble ones of degree at most one in finitely presented self-similar groups, which is what makes products with other characteristics tractable.
  affine-self-similar-coordinate-rings-are-one-dimensional: that shows the affine self-similar route cannot pass transcendence degree zero in characteristic zero; this is the positive-characteristic counterpart that does work, at transcendence degree one, for soluble groups.
  rational-linear-groups-satisfy-boone-higman: that is Zaremsky's characteristic-zero theorem through the finitely presented self-similar group Z[1/m]^n x| GL_n(Z[1/m]); this is a positive-characteristic analogue with a Borel subgroup in place of GL_n, since finite presentation there comes from Bux's theorem.
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

**ESTABLISHED.** Let `K` be a field of characteristic `p > 0` with transcendence
degree at most one over `F_p`, and let `G <= GL_n(K)` be finitely generated and
soluble. Then there are:
- a finite-index subgroup `G_1 <= G`;
- a global function field `K'`;
- a finite set `S` of places of `K'` with `|S| >= 3`, and its ring of
  `S`-integers `O_S`,

such that `G_1` is isomorphic to a subgroup of the affine Borel group

```text
A_S = O_S^n x| B_n(O_S),
```

where `B_n` denotes invertible upper triangular matrices. Moreover `A_S` is
finitely presented and self-similar.

**Example.** For Baumslag's finitely presented metabelian group
`B_p = F_p[x^±1, (1+x)^-1] x| <x, 1+x>` no passage to finite index is needed.
`B_p` is the subgroup of `A_S` for `n = 1`, `K' = F_p(x)` and `S = {0, -1, ∞}`,
where `O_S = F_p[x^±1, (1+x)^-1]` and `O_S^x = F_p^x x <x, 1+x>`.

**Credit: known over F_p(x) for special S.** Kochloukova--Sidki,
arXiv:1710.04745, Theorem A, read from the arXiv TeX source on MSI.
- *Their setting:* `A = F_p[x^±1, 1/f_1, ..., 1/f_(n-1)] <= F_p(x)`, with the
  `f_i` distinct monic irreducible polynomials, different from `x` and `x - 1`.
- *Their conclusion:* the projective upper triangular group `PU(m, A)` is
  "transitive, finite-state and state-closed". Their text adds that it is of type
  `F_n` by Bux's theorem, since the centre of `U(m, A)` is finitely generated.
- *Match:* these rings are the S-integers of `F_p(x)` with
  `S = {0, ∞, f_1, ..., f_(n-1)}`, and `PU(n+1, O_S) ≅ A_S`, as in step 5 of the
  proof. Their text notes that `x - 1` can be replaced by any irreducible `g`
  coprime to the `f_i`.
- *Consequence:* the example `B_p` below is covered by their theorem together
  with Zaremsky's Theorem 1.1.

This node extends their case to every global function field, every `S` with
`|S| >= 3`, and passage to finite index. Its self-similarity comes from
Zaremsky's Example 4.7 rather than an explicit automaton. The extension is
routine; no priority is claimed.

Inputs:
- the Kolchin--Mal'cev triangularization theorem (textbook);
- Bux's theorem on Borel subgroups over global function fields
  (`function-field-borel-groups-are-fp-for-three-places`);
- Zaremsky's self-similarity criterion for affine groups over rings with a
  finite-index principal ideal (`principal-ideal-affine-groups-are-self-similar`).

The derivation is `function-field-soluble-self-similar-proof`.
