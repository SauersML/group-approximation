---
rg: 2
id: lef-normal-amalgams-need-not-be-mf
kind: claim
title: An amalgam of two isomorphic locally residually finite groups over a common index-two normal subgroup can be finitely generated, sofic and not MF, so the LEF-factor Schafhauser tool proposed for H_mix is false
distinct_from:
  jacobson-el2-core-escapes-amenable-tree-extensions: that shows amenable-factor Schafhauser amalgams cannot certify MF for H_mix, and names an MF theorem for N-normal amalgams of LEF groups as the missing tool; this shows that tool is false as stated, even with index two, isomorphic factors and locally residually finite factors.
  ascending-hnn-finitary-linear-family-is-sofic-non-mf: that supplies the sofic non-MF group G = K x| Z used here; this repackages G, by doubling the kernel, as a subgroup of an index-two normal amalgam of two copies of K wr Z/2.
  amenable-symbol-subgroups-keep-the-jacobson-head: that uses Schafhauser's amenable-factor theorem to certify MF; this bounds how far that theorem can be extended, since LEF factors do not suffice.
artifacts:
  - experiments/h-mix-column-windows-2026-09-17/check_windows.py
---

**ESTABLISHED** (route `lef-normal-amalgams-need-not-be-mf-proof`).

## Statement

**Doubling lemma.** Let `N` be any group and `phi in Aut(N)`. On `N^2` put

```text
alpha(x, y) = (y, x),      beta(x, y) = (phi y, phi^-1 x).
```

Both are involutions, so they define an action of `D_inf = <alpha> * <beta>`, and

```text
Gamma(N, phi) = N^2 x| D_inf = (N^2 x| <alpha>) *_{N^2} (N^2 x| <beta>).
```

- `N^2` is normal of index two in both factors.
- Both factors are isomorphic to `N wr Z/2`. Indeed `beta = theta^-1 alpha theta`
  for `theta(x, y) = (x, phi y)`.
- `alpha beta = phi^-1 x phi`. So `(N x 1) x| <alpha beta>` is a copy of
  `N x|_{phi^-1} Z`, which is isomorphic to `N x|_phi Z`.

**Theorem.** Let `G = GL_fin(F_2^(V/L)) x| Q` be any member of the family
`ascending-hnn-finitary-linear-family-is-sofic-non-mf`. Let `K` be the kernel of
the stable-letter exponent `G -> Z`, and let `phi = Ad u` on `K`. Then:

1. `K` is locally residually finite, hence LEF.
2. `K wr Z/2` is locally residually finite, hence LEF.
3. `Gamma = Gamma(K, phi)` is finitely generated and sofic, and it is not MF.

So `Gamma` is an amalgam `G_1 *_W G_2` with the following properties, and it is
still not MF:
- `W = K^2` is normal of index two in each `G_i`;
- `G_1` is isomorphic to `G_2`, and both are locally residually finite;
- `Gamma` is finitely generated and sofic.

## Consequence for the MF side of HC

`jacobson-el2-core-escapes-amenable-tree-extensions` names two tools, either of
which would prove `H_mix = (W x| <a>) *_W (W x| <b>)` MF and so kill the `H_mix`
lane of HC:
- (a) an MF theorem for `N`-normal amalgams of LEF groups;
- (b) such a theorem just for `W x| D_inf`.

**Tool (a) is false.** The theorem above is a counterexample to it.

**A precise obstruction to repairing it by finite generation.** The factors
`K wr Z/2` are not finitely generated. Suppose instead that `N` is finitely
generated and residually finite. Then `N x| Z` is residually finite, because
`N` has characteristic subgroups of finite index. The doubling `Gamma(N, phi)`
is then residually finite too. So a doubling counterexample with finitely
generated factors needs `N` finitely generated, LEF and not residually finite.
That is exactly the situation of the `H_mix` core `W`
(`h-mix-halves-are-lef-by-column-windows`).

**What is left.** Tool (b) stands alone. Any MF proof for `H_mix` has to use
more of `W` than "the two halves are LEF". The "LEF plus Schafhauser" route is
closed at the level of general theorems.

DERIVATION
lef-normal-amalgams-need-not-be-mf-proof
