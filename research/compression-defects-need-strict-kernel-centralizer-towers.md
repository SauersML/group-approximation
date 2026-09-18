---
rg: 2
id: compression-defects-need-strict-kernel-centralizer-towers
kind: claim
title: Over an abelian quotient a compression defect is nontrivial exactly when a compressor strictly enlarges the kernel centralizer, so kernels with tame Kazhdan centralizer towers kill it
distinct_from:
  abelian-extensions-kill-kcf-compression-defects: that assumes the kernel centralizers of compressed images are trivial and proves vanishing; this proves the exact criterion (vanishing iff every compressor normalizes C_K(L)), so trivial centralizers are one case, and it kills kernels whose centralizers are far from trivial, such as K_1 x K_2 for Titz Mite--Witzel kernels K_i, which are not KCF.
  noetherian-invariant-compression-rigidity: that needs a chain condition on the invariant's value poset in the whole group; this needs no chain condition anywhere, gives an if-and-only-if at the level of the kernel K rather than G, and its kill needs finiteness only along one nested compression tower of Kazhdan subgroups of K.
  rigid-compression-defect-normalization-dichotomy: that equates, across an approximation class, killing rigid defects with normalizing centralizers in ultraproducts; this is a statement about a single group, over an abelian quotient, reducing normalization of C_G(L) to normalization of the kernel part C_K(L).
  defect-forces-proper-self-embedding: that extracts a proper self-embedding of the Kazhdan subgroup; this adds the dual object, a strictly compressed commuting centralizer tower in the kernel with non-finitely-generated union.
  compression-defect-dies-in-finite-dimensions: that kills the defect in every finite-dimensional representation; this kills it in every group containing, with abelian quotient, a subgroup of a finite product of KCF and linear groups, none of which need be linear.
artifacts:
  - research/abelian-extensions-kill-kcf-compression-defects.md
---

**ESTABLISHED.** Let `K normal G` with `G/K` abelian, and let `L <= K`. Use the intrinsic
compression-centralizer defect

```text
Comp_G(L) = { s in G : s L s^-1 <= L },    G_comp(L) = <Comp_G(L)>,
D_G(L)    = << [g z g^-1, l] : g in G_comp(L), z in C_G(L), l in L >>_G ,
M         = C_K(L) = K ∩ C_G(L).
```

For every `s in Comp_G(L)`:

```text
M <= s M s^-1 = C_K(s L s^-1)     and     C_G(L) <= s C_G(L) s^-1.          (CT0)
```

1. **Exact criterion.** `D_G(L) = 1` if and only if `s M s^-1 = M` for every `s in Comp_G(L)`.
   Equivalently, if and only if `G_comp(L)` normalizes `C_G(L)`.
2. **Forced tower.** If `D_G(L) != 1`, there is a compressor `s` such that
   - `s L s^-1` is strictly smaller than `L`;
   - `M < s M s^-1 < s^2 M s^-2 < ...` is an infinite strictly ascending chain of centralizers
     in `K` of the nested subgroups `L_j = s^j L s^-j`;
   - `s^-1 M s < M`, so `s^-1` strictly compresses the commuting partner `M` of `L`;
   - `M_inf = union_j s^j M s^-j` is not finitely generated and centralizes
     `L_inf = intersection_j L_j`.
3. **Finite outer order.** If the outer class of conjugation by `s` on `K` has finite order `n`,
   then some `gamma in K` satisfies `gamma L gamma^-1 < L` and `M < gamma M gamma^-1`. So the
   tower is already intrinsic to `K`.

**Tame towers.** Call `K` *Kazhdan-tower-tame* if, for every descending chain
`L_0 >= L_1 >= ...` of Kazhdan subgroups of `K`, the chain `C_K(L_0) <= C_K(L_1) <= ...` is
eventually constant. By item 2, if `K` is tame and `G/K` is torsion-free abelian, then
**`D_G(L) = 1` for every Kazhdan subgroup `L` of every such `G`.** Such an `L` lies in `K`,
because its image in `G/K` is a finite group, hence trivial.

**The tame class.** Every subgroup `H <= K_1 x ... x K_r` is tame when each `K_i` is either
- KCF (nontrivial Kazhdan subgroups have trivial centralizer), or
- linear over a field.

This covers:
- `K_1 x K_2` with each `K_i` a Titz Mite--Witzel kernel, a torsion-free hyperbolic group or a
  torsion-free cocompact CAT(0) group of dimension two (all KCF by the graph);
- fibre products and all other subgroups of such products;
- products of these with linear groups.

When `r >= 2` and at least two factors are nontrivial Kazhdan groups, `H = K_1 x K_2` is not KCF
(`K_2` centralizes `K_1`). So the KCF kill does not reach these kernels.

## What this kills

- **(EK1) and (SCZ1) on tame kernels.** `torsion-free-sofic-extrinsic-kazhdan-defect-kernel` and
  `split-cyclic-kazhdan-defect-exact-mf-radical` need `D_G(L) = K != 1` in
  `G = K semidirectProduct_phi Z`. For a tame `K` this is impossible for every `phi` and every
  Kazhdan `L`. In particular, "take a product of KCF kernels and let `phi` permute or twist the
  factors" is dead. It is the natural way to escape the KCF kill of
  `abelian-extensions-kill-kcf-compression-defects`.
  - *Invariant.* The lengths of the centralizer chains `C_K(L_j)` along nested Kazhdan towers.
  - *Step where every member dies.* `[s,z] in C_K(s L s^-1) = s M s^-1 = M`, which puts
    `s z s^-1` back into `C_G(L)`.
- **Compression certificates for (XMF).** `mf-kazhdan-quotientless-mapping-torus-exact-radical`
  asks for `Q semidirectProduct_psi Z` with radical `Q`. Any compression-defect certificate there
  (`normal-kazhdan-defect-non-mf`, Attempt 3 of that node) needs `Q` not tame. So `Q` has a
  strictly ascending non-finitely-generated tower of Kazhdan centralizers.
- **Forced biography of any witness.** A kernel `K` realizing (EK1) contains a Kazhdan `L`, an
  element `s` of `G` and a nontrivial `M = C_K(L)` such that `s` strictly compresses `L` and
  `s^-1` strictly compresses `M`. It also contains a non-finitely-generated subgroup `M_inf`
  commuting with `L_inf`. This sharpens "not KCF" to "not tame".

Proof: `compression-defects-need-strict-kernel-centralizer-towers-proof`.
