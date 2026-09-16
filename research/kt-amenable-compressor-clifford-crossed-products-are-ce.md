---
rg: 2
id: kt-amenable-compressor-clifford-crossed-products-are-ce
kind: claim
title: Every amenable Ore compressor slice of the Kun--Thom Clifford crossed product is Connes embeddable
distinct_from:
  kun-thom-clifford-crossed-product-ce: that asks for Connes embeddability of the whole algebra Cl(G/Gamma) crossed_product G; this proves it for the subalgebras over <Gamma,S> with S an amenable left Ore compressor monoid and over the actor group, and leaves G and the Laurent group E untouched.
  kt-one-compressor-full-coset-action-is-sofic: that proves soficity of the permutation action of one compressor on the ambient coset set; this proves Connes embeddability of the anticommuting Clifford crossed product over any amenable Ore compressor monoid, which no permutation-level soficity statement implies.
  kt-one-compressor-normalizer-cocycle-splits: that splits a finitary normalizer cocycle over one-compressor groups; this is an embedding theorem for the tracial Clifford algebra itself.
  heisenberg-kun-thom-slice-is-relatively-embeddable: that proves relative embeddability of L(Gamma) in L(P) for the Heisenberg slice via a sofic double; this proves the Clifford crossed product over the same slice is Connes embeddable, a statement about a different algebra.
  commuting-kun-thom-compressors-are-relatively-embeddable: that gives relative embeddability of the group von Neumann algebra inclusion for commuting slices; this gives Connes embeddability of the Clifford crossed product for all amenable left Ore slices, commuting ones included.
  one-kun-thom-compressor-is-relatively-embeddable: that is relative embeddability of L(Gamma) in L(<Gamma,A>) through a sofic amalgamated double; this is Connes embeddability of Cl(G/Gamma) crossed_product <Gamma,A> with the full ambient Clifford base.
  kt-pointed-clifford-energy-one-compressor-no-go: that builds one-compressor matrix countermodels to a weaker pointed commutator-energy inequality without anticommutation; this gives one-compressor microstates for all Clifford moments, including the anticommutation relation that node left as possible extra data.
  positive-core-bernoulli-ce: that is a commutative Bernoulli crossed product over Gamma acting on the positive part of the coset set; this is the Clifford base over the whole coset set with compressors adjoined.
  amenable-multi-compressors-have-a-joint-hs-telescope: that builds normalized-HS covariance telescopes for finite-dimensional representations over a cancellative Folner monoid; this averages a Connes embeddable von Neumann algebra over a Folner set of the amenable group <S> and yields Connes embeddability of the Clifford crossed product itself.
artifacts:
  - research/artifacts/kt-amenable-compressor-clifford-ce-2026-09-16.md
---

Use the regular finite-field Kun--Thom data, with `k` finite, `r >= 3` and
`d >= 1`.  The endpoint instance is `k = F_2`, `r = d = 3`.

```text
R_0 = k[N^d],   R = k[Z^d],   Gamma = EL_r(R_0),   E = EL_r(R),
G = E rtimes SL_d(Z),   X = G/Gamma,   L_+ = SL_d(Z) intersect M_d(N).
```

In `M = Cl(X) rtimes G`, with the canonical trace, write
`M_H = (Cl(X) union {u_h : h in H})''` for `H <= G`.

Let `S subset L_+` be a submonoid that is **left Ore**, i.e.
`Ss intersect Ss' != empty` for all `s, s'`, and such that `<S>` is
**amenable**.  Then `M_{<Gamma,S>}` is Connes embeddable.  Hence so is
`M_K` for every subgroup `K` of every conjugate of `<Gamma,S>`.  Also, `M_K`
is Connes embeddable for every `K <= G` with `K intersect E = 1`, in
particular for `K = SL_d(Z)`.

Instances:

- one compressor `<Gamma,A>`, the ascending HNN group `V_A`;
- any commuting family `<Gamma,A_1,...,A_m>`;
- the Heisenberg slice `<Gamma, I+E_12, I+E_23>` (`d >= 3`), which is left
  Ore by a polynomial count of positive words;
- more generally, any `S` generating a group of subexponential growth.

**Consequences for the target.**

- Any refutation of `kun-thom-clifford-crossed-product-ce` must use a
  subgroup contained in no conjugate of such a `<Gamma,S>`.  The Laurent
  group `E` is one such subgroup: it lies in no `N_S`, because the directed
  union of the pointed cones `s^(-1) N^d` never contains both `z` and `-z`.
  The two-compressor pair of `kt-two-positive-compressors-generate-full-obstruction`
  generates the nonamenable `SL_3(Z)`, so it is another.
- The target's parenthetical about flexible HS-stability of the ascending
  HNN subgroup `<Gamma,t>` is closed.  That subgroup is not flexibly
  HS-stable (`monomial-kazhdan-hnn-is-rf-but-non-rfd-and-not-vfhs-stable`),
  and its Clifford crossed product is Connes embeddable by this claim.

Not claimed: anything about `M_E` or `M_G`, or about amenable non-Ore
compressor monoids.

DERIVATION
kt-amenable-compressor-clifford-ce-proof
