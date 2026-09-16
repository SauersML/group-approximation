---
rg: 2
id: commuting-conjugate-switch-amenability-criterion
kind: claim
title: A commuting-conjugate coset presentation is amenable exactly when its double cosets are covered by the listed ones
distinct_from:
  finite-orbital-checksum-cannot-expose-sl3-coset-module: that uses the invariant C_2 graph-product model as a no-go for finitely many lamp checks over SL_3; this proves the exact Z-lamp isomorphism for an arbitrary finite presentation and reads off an amenability dichotomy on the bi-index cover.
  compression-wreath-not-finitely-presented: that is the finite-presentation obstruction for wreath products with infinitely many double cosets; this is an amenability switch whose positive branch is a finitely presented permutational wreath product and whose negative branch contains F_2.
  shift-raag-family-classifies-amenability: that is the recursive family over Z with infinitely many commutator relators; this is the finitely presented coset version, where finitely many relators suffice because the actor has finite bi-index cosets.
  finitely-generated-centralizer-switches-are-sigma1: that is the case U empty, where the switch event is the generation equality K = C and has finite certificates; this adds finitely many commuting-conjugate relators, so the event becomes the double-coset cover K = C cup CUC cup CU^-1C, which is not a finite packet of equations.
artifacts:
  - research/artifacts/commuting-conjugate-coset-switch-2026-09-16.md
---

ESTABLISHED by `commuting-conjugate-switch-criterion-proof`. Elementary; the
graph-product model is the one already used in
[[finite-orbital-checksum-cannot-expose-sl3-coset-module]], and no novelty is
claimed for it.

## Statement

Let `K` be a group, `C = <S_C> <= K`, and `U subset K` finite. Put `X = K/C` and

```text
Q(K,C,U) = < K, b | [b,c] (c in S_C), [b, u b u^-1] (u in U) >,
D(C,U)   = C  cup  CUC  cup  CU^-1C.
```

1. `Q(K,C,U) = A(Gamma) x| K`, where:
   - `A(Gamma)` is the right-angled Artin group on the vertex set `X`;
   - the edges of `Gamma` are the `K`-translates of the pairs `{C, uC}`;
   - `K` permutes the vertex generators;
   - `b` is the generator at the base vertex `C`.
2. `Q(K,C,U)` is amenable iff `K` is amenable and `K = D(C,U)`.
   - On the positive side, `Q = Z wr_(K/C) K`.
   - For `k notin D(C,U)`, the elements `b` and `k b k^-1` freely generate `F_2`.
3. If `K` is finitely presented and `S_C`, `U` are finite word sets, then `Q` is a
   finite presentation computed uniformly from the data.

**Switch form.** Let `e -> (K_e, S_(C_e), U_e)` be computable, with every `K_e`
amenable. Then `Q_e` is amenable exactly when `K_e = D(C_e, U_e)`. This is a
uniformly `Pi^0_2` event: every word lies in one of finitely many double cosets.
It involves infinitely many double-coset memberships, so it is not a finite
packet of equations. The amalgam `K *_C (C x Z)` has amenable locus `C = K`, by
`finite-graphs-of-amenable-groups-have-sigma1-locus`. The finitely many
relators `[b, u b u^-1]` are controller relations that raise this to the cover
event.
