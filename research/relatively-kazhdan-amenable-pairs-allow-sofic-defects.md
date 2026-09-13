---
rg: 2
id: relatively-kazhdan-amenable-pairs-allow-sofic-defects
kind: claim
title: A left-orderable sofic group carries a compression defect over a relatively Kazhdan amenable infranormal pair
invalidates: [left-orderable-non-sofic-via-relative-kazhdan-defect-criterion]
distinct_from:
  sofic-groups-kill-rigid-compression-defects: that kills defects in sofic groups when the compressed subgroup and the compressor group are both Kazhdan; this shows the conclusion fails when only relative property (T) of an amenable compressed subgroup is available, a kind of rigidity known to occur in left-orderable groups.
---

**ESTABLISHED.**  Let `p` be a prime and `D = Z[1/p]`.  Let `F_0 <= SL_2(Z)` be a
torsion-free finite-index free subgroup, for example the principal congruence
subgroup of level 3, and put

```text
Lambda = F_0 x <p I>  <= GL_2(D),     G = D^2 x| Lambda,     Gamma = Z^2 <= D^2 <= G,
H = (direct_sum_(G/Gamma) Z) x| G.
```

Then:

1. `G` and `H` are left-orderable, and even locally indicable;
2. `(G, Gamma)` has relative property (T), and `Gamma` is amenable;
3. `Gamma` is infranormal and not normal in `G`, with strict compressor
   `t = p I`;
4. `H` is sofic;
5. `H` has a nontrivial compression defect over the pair: `z = e_(Gamma)`
   centralizes `Gamma`, but `[t z t^-1, gamma] != 1` for the translation
   `gamma = v_1 = (1,0) in Gamma`.

**Consequence.**  The following "relative" version of
`sofic-groups-kill-rigid-compression-defects` is false:

> if `H` is sofic, `Gamma <= G <= H`, `(G, Gamma)` has relative property (T) and
> `Gamma` is infranormal in `G`, then `G` normalizes `C_H(Gamma)`.

It is false inside the class of left-orderable groups, where it would have been
used.  Relatively Kazhdan pairs with abelian rigid subgroup are the kind of
rigidity known to exist in groups acting on the line
(`F_2 x| Z^2`, Navas arXiv:1712.06462v2, p. 3).

**Scope.**  Here `G` is not Kazhdan.  A variant asking in addition that `G` be
Kazhdan is not refuted by this example.  A left-orderable instance of that
variant would contain an infinite left-orderable Kazhdan group, which is
`infinite-left-orderable-kazhdan-group`.

Derivation: `relatively-kazhdan-amenable-pairs-allow-sofic-defects-proof`.
